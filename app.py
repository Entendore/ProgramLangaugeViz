#!/usr/bin/env python3
"""
program_enumerator.py — generate ALL programs of length n in many languages,
keeping only the ones that pass a STATIC validity check. Nothing is ever run:
no exec/eval/subprocess anywhere — only parsers/linters touch the candidates.

Languages: Python(ast+pyflakes) JSON XML HTML Regex TOML YAML CSS SQL JS Java C
C++/Go/C#/Rust/Haskell (tree-sitter) Fortran (fparser2) Pascal Lua Bash Lisp
Brainfuck + Generic C-like.  Sound lexical NFA pruners (selftest-verified).

Visual layer
    QSS themes (light/dark) with per-language accent colours
    stat tiles · work-saved (pruned vs parsed) bar · throughput sparkline
    structure map (lexical regions + bracket-depth sparkline) · heat-grid
    overview dock · preview chips · toasts · spinner · empty-state watermark
    pause/filter/stars/export/scratchpad/QSettings persistence (as before)

Usage:
    pip install PySide6 pyflakes
    python program_enumerator.py --selftest
    python program_enumerator.py
"""

from __future__ import annotations

import argparse, ast, csv, importlib, io, itertools, json, math, os, re, sys, time
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from html.parser import HTMLParser

from PySide6.QtCore import (QEvent, QPropertyAnimation, QRegularExpression, Qt,
                            QCoreApplication, QEasingCurve, QGraphicsOpacityEffect,
                            QSettings, QThread, QTimer, Signal)
from PySide6.QtGui import (QAction, QBrush, QColor, QFont, QFontDatabase,
                           QKeySequence, QPainter, QPalette, QPen, QPointF,
                           QPolygonF, QSyntaxHighlighter, QTextCharFormat)
from PySide6.QtWidgets import (QAbstractItemView, QApplication, QCheckBox,
                               QComboBox, QDialog, QDockWidget, QFileDialog,
                               QFrame, QGridLayout, QHBoxLayout, QLabel,
                               QLineEdit, QListWidget, QListWidgetItem,
                               QMainWindow, QMenu, QMessageBox, QPlainTextEdit,
                               QProgressBar, QPushButton, QSpinBox, QSplitter,
                               QVBoxLayout, QWidget)

# --------------------------------------------------------------------------- #
# optional dependencies
# --------------------------------------------------------------------------- #
def _probe(name):
    try:
        return importlib.import_module(name)
    except Exception:
        return None

MOD = {n: _probe(n) for n in
       ("pyflakes", "esprima", "javalang", "pycparser.c_parser", "sqlglot",
        "luaparser.ast", "bashlex", "tinycss2", "yaml", "fparser.two")}
try:
    import tomllib as _toml
except Exception:
    _toml = _probe("tomli")
HAS_PYFLAKES = MOD["pyflakes"] is not None


# =========================================================================== #
# 1) Generic lexical NFA — sound prefix pruner, configured per language
# =========================================================================== #
@dataclass(frozen=True)
class SDelim:
    o: str; c: str; esc: bool = True; nl: bool = False
    dbl: bool = False
    raw: str = ""                 # "rust": r#"..."#   /  "cpp": R"delim(...)delim"

@dataclass(frozen=True)
class BComment:
    o: str; c: str; nested: bool = False

@dataclass(frozen=True)
class LexSpec:
    brackets: tuple = ()
    strings:  tuple = ()
    lcomments: tuple = ()
    bcomments: tuple = ()
    cont: str = ""

_CODE, _STR, _LCOM, _BCOM, _CONT, _STRQ, _RAWO, _RAWC = range(8)

def _suffix_prefix_len(s, pat):
    for L in range(min(len(s), len(pat)), 0, -1):
        if pat.startswith(s[-L:]):
            return L
    return 0


class GenericLexMachine:
    """NFA over lexical states; keeps every consistent interpretation."""

    def __init__(self, spec: LexSpec):
        self.spec = spec
        self.openers = {}
        for i, d in enumerate(spec.strings):   self.openers[d.o] = (_STR, i)
        for i, c in enumerate(spec.lcomments): self.openers[c] = (_LCOM, i)
        for i, c in enumerate(spec.bcomments): self.openers[c.o] = (_BCOM, i)

    def init(self):
        return frozenset({(_CODE, 0, False, 0, "", 0, 0, (0,) * len(self.spec.brackets))})

    def step(self, S, ch):
        out = set()
        for st in S:
            out |= self._feed(st, ch)
        return frozenset(out)

    def completable(self, S, remaining, alpha):
        for (k, sub, _e, run, pend, cp, _n, dep) in S:
            need, ok = 0, True
            for i, (_o, c) in enumerate(self.spec.brackets):
                if dep[i]:
                    if c not in alpha: ok = False; break
                    need += dep[i]
            if not ok: continue
            if k in (_CODE, _LCOM):
                if need <= remaining: return True
            elif k == _STR:
                d = self.spec.strings[sub]
                if set(d.c) <= alpha and need + len(d.c) - run <= remaining:
                    return True
            elif k == _STRQ:
                if run == 1:
                    if need <= remaining: return True
                else:
                    q = self.spec.strings[sub].c
                    if set(q) <= alpha and need + 1 <= remaining: return True
            elif k == _RAWO:
                d = self.spec.strings[sub]
                if d.raw == "rust":
                    if '"' in alpha and need + 2 <= remaining: return True
                else:
                    chars = set(pend) | {'(', ')', '"'}
                    if chars <= alpha and need + len(pend) + 3 <= remaining:
                        return True
            elif k == _RAWC:
                d = self.spec.strings[sub]
                P = ('"' + cp) if d.raw == "rust" else (')' + cp + '"')
                if set(P[run:]) <= alpha and need + len(P) - run <= remaining:
                    return True
            else:
                if "\n" in alpha and need + 1 <= remaining: return True
        return False

    def acceptable(self, S):
        for (k, _sub, _e, run, pend, _cp, _n, dep) in S:
            if k == _LCOM:
                return True
            if k == _STRQ and run == 1 and sum(dep) == 0:
                return True
            if k == _CODE and sum(dep) == 0 and \
               any(t.startswith(pend) for t in self.spec.lcomments):
                return True
        return False

    def _depth_step(self, dep, ch):
        for i, (o, c) in enumerate(self.spec.brackets):
            if ch == o:
                dep = dep[:i] + (dep[i] + 1,) + dep[i + 1:]
            elif ch == c:
                if dep[i] <= 0: return None
                dep = dep[:i] + (dep[i] - 1,) + dep[i + 1:]
        return dep

    def _plain(self, dep, ch):
        if self.spec.cont and ch == self.spec.cont:
            return ((_CONT, 0, False, 0, "", 0, 0, dep),)
        nd = self._depth_step(dep, ch)
        return () if nd is None else ((_CODE, 0, False, 0, "", 0, 0, nd),)

    def _enter(self, op, rest, dep):
        kind, idx = op
        if kind == _STR:
            d = self.spec.strings[idx]
            cur = {(_RAWO if d.raw else _STR, idx, False, 0, "", 0, 0, dep)}
        elif kind == _LCOM:
            cur = {(_LCOM, idx, False, 0, "", 0, 0, dep)}
        else:
            cur = {(_BCOM, idx, False, 0, "", 0, 1, dep)}
        for c in rest:
            nxt = set()
            for s in cur: nxt |= self._feed(s, c)
            cur = nxt
            if not cur: break
        return cur

    def _feed(self, st, ch):
        k, sub, esc, run, pend, cp, nest, dep = st
        spec = self.spec
        if k == _STR:
            d = spec.strings[sub]
            if esc:
                return {(_STR, sub, False, 0, "", cp, 0, dep)}
            if d.esc and ch == "\\":
                return {(_STR, sub, True, 0, "", cp, 0, dep)}
            if ch == "\n" and not d.nl:
                return set()
            if d.dbl:
                if ch == d.c:
                    return {(_STRQ, sub, False, 1, "", cp, 0, dep)}
                return {(_STR, sub, False, 0, "", cp, 0, dep)}
            if run < len(d.c) and ch == d.c[run]:
                if run + 1 == len(d.c):
                    return {(_CODE, 0, False, 0, "", 0, 0, dep)}
                return {(_STR, sub, False, run + 1, "", cp, 0, dep)}
            r2 = _suffix_prefix_len(d.c[:run] + ch, d.c)
            return {(_STR, sub, False, r2, "", cp, 0, dep)}
        if k == _STRQ:
            d = spec.strings[sub]
            if ch == d.c:
                return {(_STRQ, sub, False, 2 if run == 1 else 1, "", cp, 0, dep)}
            if run == 2:
                return self._feed((_STR, sub, False, 0, "", cp, 0, dep), ch)
            return self._plain(dep, ch)
        if k == _RAWO:
            d = spec.strings[sub]
            if d.raw == "rust":
                if ch == "#":
                    if len(pend) >= 32: return set()
                    return {(_RAWO, sub, False, 0, pend + "#", cp, 0, dep)}
                if ch == '"':
                    return {(_RAWC, sub, False, 0, "", pend, 0, dep)}
                return set()
            if ch == "(":
                return {(_RAWC, sub, False, 0, "", pend, 0, dep)}
            if ch in " \\()\n\r\t" or len(pend) >= 16:
                return set()
            return {(_RAWO, sub, False, 0, pend + ch, cp, 0, dep)}
        if k == _RAWC:
            d = spec.strings[sub]
            P = ('"' + cp) if d.raw == "rust" else (')' + cp + '"')
            if run < len(P) and ch == P[run]:
                if run + 1 == len(P):
                    return {(_CODE, 0, False, 0, "", 0, 0, dep)}
                return {(_RAWC, sub, False, run + 1, "", cp, 0, dep)}
            r2 = _suffix_prefix_len(P[:run] + ch, P)
            return {(_RAWC, sub, False, r2, "", cp, 0, dep)}
        if k == _LCOM:
            return {(_CODE, 0, False, 0, "", 0, 0, dep)} if ch == "\n" else {st}
        if k == _BCOM:
            bc = spec.bcomments[sub]
            buf = cp + ch
            L = max(len(bc.o), len(bc.c))
            if bc.nested and buf.endswith(bc.o):
                return {(_BCOM, sub, False, 0, "", "", nest + 1, dep)}
            if buf.endswith(bc.c):
                if nest == 1:
                    return {(_CODE, 0, False, 0, "", 0, 0, dep)}
                return {(_BCOM, sub, False, 0, "", "", nest - 1, dep)}
            return {(_BCOM, sub, False, 0, "", buf[-(L - 1):] if L > 1 else "",
                     nest, dep)}
        if k == _CONT:
            return {(_CODE, 0, False, 0, "", 0, 0, dep)} if ch == "\n" else set()

        out, cand = set(), pend + ch
        if any(t.startswith(cand) for t in self.openers):
            out.add((_CODE, 0, False, 0, cand, 0, 0, dep))
        for i in range(1, len(pend) + 1):
            pre = pend[:i]
            if pre in self.openers:
                out |= self._enter(self.openers[pre], pend[i:] + ch, dep)
        if cand in self.openers:
            out |= self._enter(self.openers[cand], "", dep)
        cur = (_CODE, 0, False, 0, "", 0, 0, dep)
        for c2 in pend + ch:
            r = self._plain(cur[7], c2)
            if not r:
                return out
            cur = r[0]
        out.add(cur)
        return out


# =========================================================================== #
# 2) Specialised machines: markup (HTML/XML) and regex
# =========================================================================== #
class MarkupMachine:
    def __init__(self, void=frozenset(), ci=True, lt_text=True):
        self.void, self.ci, self.lt_text = void, ci, lt_text

    def init(self): return frozenset({(0, "", "", (), "")})

    def _nm(self, s): return s.lower() if self.ci else s

    def step(self, S, ch):
        out = set()
        for (w, q, buf, stack, cp) in S:
            if w == 2:
                b = (cp + ch)[-3:]
                if b.endswith("-->"): out.add((0, "", "", stack, ""))
                else:                 out.add((2, q, buf, stack, b))
            elif w == 1:
                if q:
                    out.add((1, "" if ch == q else q, buf, stack, ""))
                elif ch in "\"'":
                    out.add((1, ch, buf, stack, ""))
                elif ch == ">":
                    b = buf.strip()
                    if b.startswith("/"):
                        nm = self._nm(b[1:].strip())
                        if not stack or stack[-1] != nm:
                            continue
                        out.add((0, "", "", stack[:-1], ""))
                    else:
                        sc = b.endswith("/")
                        core = b[:-1] if sc else b
                        parts = core.split()
                        nm = self._nm(parts[0]) if parts else ""
                        if nm[:1] in ("!", "?") or not nm or sc or nm in self.void:
                            out.add((0, "", "", stack, ""))
                        else:
                            out.add((0, "", "", stack + (nm,), ""))
                else:
                    out.add((1, q, (buf + ch)[-64:], stack, ""))
            else:
                b = cp + ch
                if b.endswith("<!--"):
                    out.add((2, "", "", stack, ""))
                elif ch == "<":
                    out.add((1, "", "", stack, ""))
                    if self.lt_text:
                        out.add((0, "", "", stack, b[-3:]))
                else:
                    out.add((0, "", "", stack, b[-3:]))
        return frozenset(out)

    def completable(self, S, remaining, alpha):
        for (w, q, _buf, _stack, cp) in S:
            if w == 0:
                return True
            if w == 2:
                if set("-->") <= alpha and \
                   remaining >= 3 - _suffix_prefix_len(cp, "-->"):
                    return True
            else:
                need = 2 if q else 1
                if ">" in alpha and (not q or q in alpha) and remaining >= need:
                    return True
        return False

    def acceptable(self, S):
        return any(w == 0 for (w, *_rest) in S)


class RegexMachine:
    def init(self): return frozenset({(False, False, 0, False, False)})

    def step(self, S, ch):
        out = set()
        for (ic, esc, d, cs, cc) in S:
            if ic:
                if esc:   out.add((True, False, d, True, cc))
                elif ch == "\\": out.add((True, True, d, cs, cc))
                elif ch == "]":
                    if (not cs and not cc) or (cc and not cs):
                        out.add((True, False, d, True, cc))
                    else:
                        out.add((False, False, d, False, False))
                elif ch == "^" and not cs and not cc:
                    out.add((True, False, d, cs, True))
                else:
                    out.add((True, False, d, True, cc))
            else:
                if esc:   out.add((False, False, d, cs, cc))
                elif ch == "\\": out.add((False, True, d, cs, cc))
                elif ch == "[":  out.add((True, False, d, False, False))
                elif ch == "(":  out.add((False, False, d + 1, cs, cc))
                elif ch == ")":
                    if d <= 0: continue
                    out.add((False, False, d - 1, cs, cc))
                else:            out.add((False, False, d, cs, cc))
        return frozenset(out)

    def completable(self, S, remaining, alpha):
        for (ic, _e, d, _cs, _cc) in S:
            if ic:
                if "]" in alpha and remaining >= 1: return True
            else:
                if (d == 0 or ")" in alpha) and remaining >= d: return True
        return False

    def acceptable(self, S):
        return any((not ic) and d == 0 and not e for (ic, e, d, *_x) in S)


def run_machine_ok(machine, src):
    S = machine.init()
    for ch in src:
        S = machine.step(S, ch)
        if not S:
            return False, ["structural error: unbalanced or unterminated construct"]
    if machine.acceptable(S):
        return True, []
    return False, ["structural error: construct left open at end of input"]


# =========================================================================== #
# 3) Validators (static only — nothing is ever executed)
# =========================================================================== #
def v_python(src):
    try:
        ast.parse(src)
    except SyntaxError as e:
        return False, [f"SyntaxError: {e.msg} (line {e.lineno}, col {e.offset})"]
    except Exception as e:
        return False, [repr(e)]
    return True, []

def v_json(src):
    try:
        json.loads(src); return True, []
    except Exception as e:
        return False, [f"JSON: {e}"]

def v_xml(src):
    try:
        ET.fromstring(src); return True, []
    except ET.ParseError as e:
        return False, [f"XML: {e}"]

class _HTMLCheck(HTMLParser):
    VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input",
            "link", "meta", "param", "source", "track", "wbr"}
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.stack, self.errors = [], []
    def handle_starttag(self, tag, attrs):
        if tag not in self.VOID: self.stack.append(tag)
    def handle_startendtag(self, tag, attrs):
        pass
    def handle_endtag(self, tag):
        if self.stack and self.stack[-1] == tag:
            self.stack.pop()
        else:
            top = self.stack[-1] if self.stack else "nothing open"
            self.errors.append(f"mismatched </{tag}> (expected </{top}>)")
    def finish(self):
        self.close()
        if self.stack:
            self.errors.append(f"unclosed tag(s): {', '.join(self.stack)}")
        return self.errors

def v_html(src):
    try:
        chk = _HTMLCheck(); chk.feed(src)
        errs = chk.finish()
    except Exception as e:
        return False, [f"HTML: {e!r}"]
    return (not errs), [f"HTML: {m}" for m in errs]

def v_regex(src):
    try:
        re.compile(src); return True, []
    except Exception as e:
        return False, [f"regex: {e}"]

def v_bf(src):
    d = 0
    for i, ch in enumerate(src):
        if ch == "[": d += 1
        elif ch == "]":
            d -= 1
            if d < 0:
                return False, [f"Brainfuck: stray ']' at position {i}"]
    if d:
        return False, [f"Brainfuck: {d} unclosed '['"]
    extra = set(src) - set("+-<>[],.")
    return True, ([f"note: non-Brainfuck chars present: {''.join(sorted(extra))!r}"]
                  if extra else [])

def v_toml(src):
    if _toml is None:
        return False, ["TOML needs Python 3.11+ (tomllib) or `pip install tomli`"]
    try:
        _toml.loads(src); return True, []
    except Exception as e:
        return False, [f"TOML: {e}"]

def v_yaml(src):
    y = MOD["yaml"]
    if y is None:
        return False, ["YAML needs PyYAML: pip install pyyaml"]
    try:
        y.safe_load(src)
    except Exception as e:
        return False, [f"YAML: {e}"]
    return True, ["note: YAML accepts most text — 'valid' = parseable document"]

def v_css(src):
    t = MOD["tinycss2"]
    if t is not None:
        errs = []
        def walk(nodes):
            for nd in nodes or ():
                if type(nd).__name__ == "ParseError":
                    errs.append(getattr(nd, "message", str(nd)))
                for attr in ("content", "prelude", "rules", "declarations"):
                    sub = getattr(nd, attr, None)
                    if isinstance(sub, list): walk(sub)
        walk(t.parse_stylesheet(src, skip_comments=True, skip_whitespace=True))
        return (not errs), [f"CSS: {m}" for m in errs]
    ok, msgs = run_machine_ok(CSS_MACHINE, src)
    return ok, msgs + ["tinycss2 not installed — structural check only"]

def v_sql(src):
    sg = MOD["sqlglot"]
    if sg is None:
        return False, ["SQL needs sqlglot: pip install sqlglot"]
    try:
        exprs = sg.parse(src, read="sqlite")
        if any(e is None for e in exprs):
            return False, ["SQL: incomplete statement"]
        return True, []
    except Exception as e:
        return False, [f"SQL: {e}"]

def v_js(src):
    ep = MOD["esprima"]
    if ep is None:
        return False, ["JavaScript needs esprima: pip install esprima"]
    try:
        ep.parseScript(src); return True, []
    except Exception as e:
        return False, [f"JS: {e}"]

def v_java(src):
    jl = MOD["javalang"]
    if jl is None:
        return False, ["Java needs javalang: pip install javalang"]
    try:
        jl.parse.parse(src); return True, []
    except Exception as e:
        return False, [f"Java: {e}"]

_CPARSER = None
def v_c(src):
    pc = MOD["pycparser.c_parser"]
    if pc is None:
        return False, ["C needs pycparser: pip install pycparser"]
    global _CPARSER
    if _CPARSER is None:
        _CPARSER = pc.CParser()
    try:
        _CPARSER.parse(src); return True, []
    except Exception as e:
        return False, [f"C: {e}"]

def v_lua(src):
    la = MOD["luaparser.ast"]
    if la is None:
        return False, ["Lua needs luaparser: pip install luaparser"]
    try:
        la.parse(src); return True, []
    except Exception as e:
        return False, [f"Lua: {e}"]

def v_bash(src):
    bl = MOD["bashlex"]
    if bl is not None:
        try:
            bl.parse(src); return True, []
        except Exception as e:
            return False, [f"bash: {e}"]
    ok, msgs = run_machine_ok(BASH_FALLBACK_MACHINE, src)
    return ok, msgs + ["bashlex not installed — rough structural check only "
                       "(heredocs & quoting subtleties not understood)"]

_TS = {}
def _ts_parser(gram_mod):
    if gram_mod in _TS:
        return _TS[gram_mod]
    p = None
    try:
        ts = importlib.import_module("tree_sitter")
        gm = importlib.import_module(gram_mod)
        lang = None
        if hasattr(gm, "language"):
            cap = gm.language()
            try:
                lang = ts.Language(cap)
            except Exception:
                try:
                    lang = ts.Language(cap, gram_mod)
                except Exception:
                    lang = None
        if lang is not None:
            p = ts.Parser()
            try:
                p.language = lang
            except Exception:
                p.set_language(lang)
    except Exception:
        p = None
    _TS[gram_mod] = p
    return p

def _make_ts_validator(gram_mod, label):
    def v(src):
        p = _ts_parser(gram_mod)
        if p is None:
            return None
        try:
            tree = p.parse(src.encode("utf-8"))
        except Exception as e:
            return False, [f"{label}: parser failure {e!r}"]
        if tree.root_node.has_error:
            return False, [f"{label}: syntax error (tree-sitter)"]
        return True, []
    return v

_FP = {"parser": None, "failed": False}
def _fortran_parser():
    if _FP["failed"]:
        return None
    if _FP["parser"] is None:
        try:
            from fparser.two.parser import ParserFactory
            _FP["parser"] = ParserFactory().create(std="f2008")
        except Exception:
            _FP["failed"] = True
            return None
    return _FP["parser"]

def v_fortran(src):
    if MOD["fparser.two"] is None:
        return None
    parser = _fortran_parser()
    if parser is None:
        return None
    from fparser.common.readfortran import FortranStringReader
    try:
        from fparser.two.utils import FortranSyntaxError
    except Exception:
        class FortranSyntaxError(Exception): pass
    try:
        reader = FortranStringReader(src, ignore_comments=True)
    except Exception:
        return False, ["Fortran: unreadable input"]
    try:
        parser(reader)
        return True, []
    except FortranSyntaxError:
        pass
    except Exception:
        pass
    try:
        from fparser.two.Fortran2003 import Specification_Part, Execution_Part
    except Exception:
        return False, ["Fortran: fparser2 rules unavailable"]
    for rule in (Specification_Part, Execution_Part):
        try:
            if rule(src) is not None:
                return True, ["note: accepted as Fortran snippet "
                              "(not a full program unit)"]
        except Exception:
            continue
    return False, ["Fortran: syntax error (fparser2, std=f2008, free form)"]

def v_pascal(src):
    return run_machine_ok(PASCAL_MACHINE, src)


# =========================================================================== #
# 4) Language registry
# =========================================================================== #
HTML_VOID = _HTMLCheck.VOID

PY_SPEC = LexSpec(
    brackets=(("(", ")"), ("[", "]"), ("{", "}")),
    strings=(SDelim("'", "'", True, False), SDelim('"', '"', True, False),
             SDelim("'''", "'''", True, True), SDelim('"""', '"""', True, True)),
    lcomments=("#",), cont="\\")

def c_spec(brackets=(("(", ")"), ("[", "]"), ("{", "}")),
           strings=(SDelim("'", "'", True, False), SDelim('"', '"', True, False)),
           lcomments=("//",), bcomments=(BComment("/*", "*/"),), cont=""):
    return LexSpec(brackets, strings, lcomments, bcomments, cont)

JS_SPEC   = c_spec(strings=(SDelim("'", "'", True, False), SDelim('"', '"', True, False),
                            SDelim("`", "`", True, True)))
JAVA_SPEC = c_spec(strings=(SDelim("'", "'", True, False), SDelim('"', '"', True, False),
                            SDelim('"""', '"""', True, True)))
C_SPEC    = c_spec(cont="\\")
GEN_SPEC  = c_spec()

CPP_SPEC = LexSpec(
    brackets=(("(", ")"), ("[", "]"), ("{", "}")),
    strings=(SDelim('"', '"', True, False), SDelim("'", "'", True, False),
             SDelim('R"', ')"', False, True, raw="cpp")),
    lcomments=("//",), bcomments=(BComment("/*", "*/"),), cont="\\")

GO_SPEC = LexSpec(
    brackets=(("(", ")"), ("[", "]"), ("{", "}")),
    strings=(SDelim('"', '"', True, False), SDelim("'", "'", True, False),
             SDelim("`", "`", False, True)),
    lcomments=("//",), bcomments=(BComment("/*", "*/", nested=True),))

CSHARP_SPEC = LexSpec(
    brackets=(("(", ")"), ("[", "]"), ("{", "}")),
    strings=(SDelim('"', '"', True, False),
             SDelim('@"', '"', False, True, dbl=True),
             SDelim("'", "'", True, False)),
    lcomments=("//",), bcomments=(BComment("/*", "*/"),))

RUST_SPEC = LexSpec(
    brackets=(("(", ")"), ("[", "]"), ("{", "}")),
    strings=(SDelim('"', '"', True, False), SDelim("'", "'", True, False),
             SDelim("r", '"', False, True, raw="rust")),
    lcomments=("//",), bcomments=(BComment("/*", "*/", nested=True),))

HASKELL_SPEC = LexSpec(
    brackets=(("(", ")"), ("[", "]"), ("{", "}")),
    strings=(SDelim('"', '"', True, False), SDelim("'", "'", True, False)),
    lcomments=(),
    bcomments=(BComment("{-", "-}", nested=True),))

FORTRAN_SPEC = LexSpec(
    brackets=(("(", ")"), ("[", "]")),
    strings=(SDelim("'", "'", False, False, dbl=True),
             SDelim('"', '"', False, False, dbl=True)),
    lcomments=("!",),)

PASCAL_SPEC = LexSpec(
    brackets=(("(", ")"), ("[", "]")),
    strings=(SDelim("'", "'", False, False, dbl=True),),
    lcomments=("//",), bcomments=(BComment("{", "}"), BComment("(*", "*)")))

SQL_SPEC  = LexSpec(brackets=(("(", ")"), ("[", "]")),
                    strings=(SDelim("'", "'", False, False, dbl=True),
                             SDelim('"', '"', False, False, dbl=True),
                             SDelim("`", "`", False, False, dbl=True)),
                    lcomments=("--",), bcomments=(BComment("/*", "*/"),))
LUA_SPEC  = LexSpec(brackets=(("(", ")"), ("{", "}")),
                    strings=(SDelim("'", "'", True, False), SDelim('"', '"', True, False),
                             SDelim("[[", "]]", False, True)),
                    lcomments=("--",), bcomments=(BComment("--[[", "]]", nested=True),))
TOML_SPEC = LexSpec(brackets=(("{", "}"), ("[", "]")),
                    strings=(SDelim('"', '"', True, False), SDelim("'''", "'''", False, True),
                             SDelim("'", "'", False, False), SDelim('"""', '"""', False, True)),
                    lcomments=("#",))
CSS_SPEC  = c_spec(strings=(SDelim("'", "'", True, False), SDelim('"', '"', True, False)))
BF_SPEC   = LexSpec(brackets=(("[", "]"),))
LISP_SPEC = LexSpec(brackets=(("(", ")"), ("[", "]")),
                    strings=(SDelim('"', '"', True, False),), lcomments=(";",))
BASH_FALLBACK_SPEC = LexSpec(strings=(SDelim("'", "'", False, True), SDelim('"', '"', True, True)),
                             lcomments=("#",), cont="\\")

CSS_MACHINE           = GenericLexMachine(CSS_SPEC)
BASH_FALLBACK_MACHINE = GenericLexMachine(BASH_FALLBACK_SPEC)
PASCAL_MACHINE        = GenericLexMachine(PASCAL_SPEC)

class Language:
    def __init__(self, key, name, engine, validate, machine=None, deps=(),
                 note="sound lexical NFA pruner", presets=None, pyflakes=False,
                 optional=(), live=None):
        self.key, self.name, self.engine = key, name, engine
        self._validate, self._machine = validate, machine
        self.deps, self.optional, self.live = deps, optional, live
        self.note, self.presets, self.pyflakes = note, presets or {}, pyflakes
        self.missing = [(i, p) for i, p in deps if _probe(i) is None]
        self.available = not self.missing
        self.emoji, self.hue = "•", 210

    def make_machine(self):
        return self._machine() if callable(self._machine) else self._machine

    def validate(self, src):
        try:
            res = self._validate(src)
        except Exception as e:
            return False, [f"validator error: {e!r}"]
        if res is None:
            m = self.make_machine()
            if m is None:
                return False, ["validator unavailable"]
            ok, msgs = run_machine_ok(m, src)
            return ok, msgs + ["note: primary engine unavailable — "
                               "structural fallback used"]
        return res

LANGS = [
    Language("python", "Python", "ast.parse (+ optional pyflakes)", v_python,
             lambda: GenericLexMachine(PY_SPEC), presets={
                "chars": [("arithmetic", "()+-*/0123456789"),
                          ("quotes & strings", "1+'\""),
                          ("comments & continuation", "1+#\\\n "),
                          ("names & keywords", "print x ( ) = 1 + if else :")],
                "tokens": [("mini python", "print ( x ) = 1 +"),
                           ("control flow", "if x > 1 : print ( ) else")]},
             pyflakes=True),
    Language("json", "JSON", "json.loads (stdlib)", v_json,
             lambda: GenericLexMachine(LexSpec(
                 brackets=(("{", "}"), ("[", "]")),
                 strings=(SDelim('"', '"', True, False),))), presets={
                "chars": [("objects & arrays", '{}[]",:123 ')],
                "tokens": [("json tokens", '" a " { } [ ] : 1 ,')]}),
    Language("xml", "XML", "xml.etree.ElementTree (stdlib)", v_xml,
             lambda: MarkupMachine(void=frozenset(), ci=False, lt_text=False),
             note="sound tag-stack pruner", presets={
                "chars": [("elements & attrs", "<a>/=1")],
                "tokens": [("xml tokens", "<a> </a> <b/> text")]}),
    Language("html", "HTML", "html.parser + tag-stack well-formedness (stdlib)",
             v_html, lambda: MarkupMachine(HTML_VOID, ci=True, lt_text=True),
             note="sound tag-stack pruner (void elements honoured)", presets={
                "chars": [("tags & attrs", "<ab>/=1 ")],
                "tokens": [("html tokens", "<html> </html> <br> <img> text")]}),
    Language("regex", "Regex", "re.compile (stdlib)", v_regex, RegexMachine,
             note="sound pruner (groups + char classes)", presets={
                "chars": [("groups & classes", "()[]a1\\^"),
                          ("quantifiers", "a1+*?{}")],
                "tokens": [("regex tokens", "( ) [ ] a 1 + * ^")]}),
    Language("brainfuck", "Brainfuck", "bracket/balance check (stdlib)", v_bf,
             lambda: GenericLexMachine(BF_SPEC),
             note="sound pruner ([] balance)", presets={
                "chars": [("brainfuck", "[]<>+-.,""" + "\"")],
                "tokens": [("bf tokens", "[ ] + - < >")]}),
    Language("lisp", "Lisp / Scheme", "structural paren/string check", None,
             lambda: GenericLexMachine(LISP_SPEC),
             note="sound pruner", presets={
                "chars": [("lisp", "()define+1 "), ("quoted", "()'\"a;")],
                "tokens": [("lisp tokens", "( ) define x 1 + quote")]})
]

_LISP_MACHINE = GenericLexMachine(LISP_SPEC)
LANGS[-1]._validate = lambda src: run_machine_ok(_LISP_MACHINE, src)
LANGS[-1].engine = "structural check (stdlib)"

LANGS += [
    Language("toml", "TOML", "tomllib (3.11+) / tomli", v_toml,
             lambda: GenericLexMachine(TOML_SPEC), presets={
                "chars": [("tables & keys", '[a]=1" '), ("inline", "[a] { } = 1")],
                "tokens": [("toml tokens", '[ ] a = 1 "')]},
             optional=(("tomli", "tomli"),)),
    Language("yaml", "YAML", "PyYAML safe_load", v_yaml, None,
             deps=(("yaml", "pyyaml"),),
             note="no prefix pruning (context-sensitive grammar) — leaf-only",
             presets={"chars": [("mappings", "a:-1 "), ("flow", "a:{[]}1")],
                      "tokens": [("yaml tokens", 'a : - 1 " { }')]}),
    Language("css", "CSS", "tinycss2 (fallback: structural check)", v_css,
             lambda: GenericLexMachine(CSS_SPEC), presets={
                "chars": [("rules", "a{}:;1px "), ("colours", "a{color:red;}")],
                "tokens": [("css tokens", "a { } : ; 1 px red")]},
             optional=(("tinycss2", "tinycss2"),)),
    Language("sql", "SQL (sqlite dialect)", "sqlglot.parse (sqlite)", v_sql,
             lambda: GenericLexMachine(SQL_SPEC), deps=(("sqlglot", "sqlglot"),),
             presets={"chars": [("select", "select*from where=1'"),
                                ("ddl", "create table ( ) , ;")],
                      "tokens": [("sql tokens", "SELECT * FROM t WHERE = 1 ( ) ;")]}),
    Language("javascript", "JavaScript", "esprima.parseScript", v_js,
             lambda: GenericLexMachine(JS_SPEC), deps=(("esprima", "esprima"),),
             presets={"chars": [("vars & calls", "var=;(){}1a+"),
                                ("template strings", "a`1${}")],
                      "tokens": [("js tokens", "var x = 1 ; function ( ) { } +")]}),
    Language("java", "Java", "javalang.parse", v_java,
             lambda: GenericLexMachine(JAVA_SPEC), deps=(("javalang", "javalang"),),
             presets={"chars": [("classes", "int=;(){}1a."), ('strings', 'a"1+" ')],
                      "tokens": [("java tokens", "int x = 1 ; { } ( ) class")]}),
    Language("c", "C", "pycparser.CParser.parse", v_c,
             lambda: GenericLexMachine(C_SPEC), deps=(("pycparser.c_parser", "pycparser"),),
             presets={"chars": [("statements", "int=;(){}1*"), ("pointers", "int* x = 1 ; ( )")],
                      "tokens": [("c tokens", "int x = 1 ; { } ( ) *")]}),
    Language("cpp", "C++", "tree-sitter-cpp (fallback: structural)",
             _make_ts_validator("tree_sitter_cpp", "C++"),
             lambda: GenericLexMachine(CPP_SPEC),
             optional=(("tree_sitter", "tree-sitter"),
                       ("tree_sitter_cpp", "tree-sitter-cpp")),
             live=lambda: _ts_parser("tree_sitter_cpp") is not None,
             note="sound pruner incl. R\"delim(...)delim\" raw strings, line splices",
             presets={"chars": [("statements", 'intmain(){};<<=1*"R'),
                                ("classes", "classpublic(){;};:1")],
                      "tokens": [("main", "int main ( ) { return 1 ; }"),
                                 ("streams", "std cout << << endl ; int ( ) { }")]}),
    Language("go", "Go", "tree-sitter-go (fallback: structural)",
             _make_ts_validator("tree_sitter_go", "Go"),
             lambda: GenericLexMachine(GO_SPEC),
             optional=(("tree_sitter", "tree-sitter"),
                       ("tree_sitter_go", "tree-sitter-go")),
             live=lambda: _ts_parser("tree_sitter_go") is not None,
             note="sound pruner; Go block comments nest, ` raw strings span lines",
             presets={"chars": [("functions & blocks", 'funcPrintln(){};="1'),
                                ("raw strings", 'funcPrintln(){};=`"1')],
                      "tokens": [("hello world-ish", 'func main ( ) { Println ( " ) ; }'),
                                 ("control flow", "package import func var if else for range : = return")]},),
    Language("csharp", "C#", "tree-sitter-c-sharp (fallback: structural)",
             _make_ts_validator("tree_sitter_c_sharp", "C#"),
             lambda: GenericLexMachine(CSHARP_SPEC),
             optional=(("tree_sitter", "tree-sitter"),
                       ("tree_sitter_c_sharp", "tree-sitter-c-sharp")),
             live=lambda: _ts_parser("tree_sitter_c_sharp") is not None,
             note="sound pruner incl. @\"...\" verbatim strings (\"\" escapes)",
             presets={"chars": [("classes & calls", 'usingSystem;Console(){}="1.'),
                                ("verbatim strings", 'Console(){};=@"1"')],
                      "tokens": [("hello world-ish", 'using System ; Console WriteLine ( ) ; " class { } = 1'),
                                 ("classes", "public class Main static void int string ( ) { } = ;")]},),
    Language("rust", "Rust", "tree-sitter-rust (fallback: structural)",
             _make_ts_validator("tree_sitter_rust", "Rust"),
             lambda: GenericLexMachine(RUST_SPEC),
             optional=(("tree_sitter", "tree-sitter"),
                       ("tree_sitter_rust", "tree-sitter-rust")),
             live=lambda: _ts_parser("tree_sitter_rust") is not None,
             note="sound pruner incl. r / r#* raw strings; block comments nest",
             presets={"chars": [("functions", 'fnmain(){};!=1"<#'),
                                ("raw strings", 'fnmain(){};!=1r#"')],
                      "tokens": [("hello world-ish", 'fn main ( ) { println ! ( " ) ; }'),
                                 ("let & mut", "fn let mut if else match loop return : = ; { } ( )")]},),
    Language("haskell", "Haskell", "tree-sitter-haskell (fallback: structural)",
             _make_ts_validator("tree_sitter_haskell", "Haskell"),
             lambda: GenericLexMachine(HASKELL_SPEC),
             optional=(("tree_sitter", "tree-sitter"),
                       ("tree_sitter_haskell", "tree-sitter-haskell")),
             live=lambda: _ts_parser("tree_sitter_haskell") is not None,
             note=("sound pruner; '--' NOT modelled as a comment (it is also a "
                   "legal operator) — only nesting {- -} comments are used"),
             presets={"chars": [("main & IO", 'main=putStrLn"1()do'),
                                ("layout & lists", "letinwhere[](){}:+1a'")],
                      "tokens": [("main", "main = do putStrLn ( )"),
                                 ("bindings", "let in where main x = 1 + ( ) [ ]")]},),
    Language("fortran", "Fortran (free-form f2008)", "fparser2 (fallback: structural)",
             v_fortran,
             lambda: GenericLexMachine(FORTRAN_SPEC),
             optional=(("fparser.two", "fparser2"),),
             live=lambda: MOD["fparser.two"] is not None,
             note=("sound pruner; ''/\"\" doubling modelled exactly; '!' comments; "
                   "'&' continuations not modelled"),
             presets={"chars": [("program skeleton", "programendimplicitnone()*,*'1=!\" "),
                                ("write statements", "write(*,*)'1readprint,=")],
                      "tokens": [("program", "program end write ( * ) ' 1 , = implicit none"),
                                 ("types", "integer real character :: = 1 ( ) ,")]},),
    Language("pascal", "Pascal", "structural check (no Python parser on PyPI)",
             v_pascal,
             lambda: GenericLexMachine(PASCAL_SPEC),
             note="sound pruner; '' doubling; { } and (* *) comments; // line comments",
             presets={"chars": [("program skeleton", "beginend.writeln();.'1=:"),
                                ("comments", "begin{}(*)//;'1end.")],
                      "tokens": [("skeleton", "begin end . writeln ( ) ; ' var : = 1"),
                                 ("control", "begin if then else while do end ; : = ( )")]},),
    Language("lua", "Lua", "luaparser.ast.parse", v_lua,
             lambda: GenericLexMachine(LUA_SPEC), deps=(("luaparser.ast", "luaparser"),),
             presets={"chars": [("lua", "print=1()x"), ("long strings", "a[[ ]]1+")],
                      "tokens": [("lua tokens", "print ( x ) = 1 + function end")]}),
    Language("bash", "Bash", "bashlex.parse (fallback: rough structural)", v_bash,
             None, presets={"chars": [("commands", "echo ls-1$ "), ("quotes", "a\"1$' ")],
                            "tokens": [("bash tokens", "echo ls = 1 $ \" ( )")]},
             note="no prefix pruning (heredocs) — leaf-only"),
    Language("generic", "Generic (any C-like)", "structural balance check", None,
             lambda: GenericLexMachine(GEN_SPEC),
             note="sound pruner — decent approximation for Go/Rust/PHP/…",
             presets={"chars": [("c-like", "{}()[];1a=+"), ("comments", "{}()/* 1a")],
                      "tokens": [("generic tokens", "{ } ( ) [ ] 1 + = ;")]})
]
GEN_MACHINE = GenericLexMachine(GEN_SPEC)
LANGS[-1]._validate = lambda src: run_machine_ok(GEN_MACHINE, src)
LANGS[-1].engine = "structural check (stdlib)"

LANG_BY_KEY = {l.key: l for l in LANGS}

EMOJI = {"python": "🐍", "json": "🧾", "xml": "🗂", "html": "🌍", "regex": "⁂",
         "brainfuck": "🧠", "lisp": "()", "toml": "⚙", "yaml": "📋", "css": "🎨",
         "sql": "🗃", "javascript": "🟨", "java": "☕", "c": "C", "cpp": "C++",
         "go": "🐹", "csharp": "♯", "rust": "🦀", "haskell": "λ", "fortran": "🔢",
         "pascal": "∆", "lua": "🌙", "bash": "🐚", "generic": "⬛"}
HUE = {"python": 42, "json": 205, "xml": 282, "html": 24, "regex": 320,
       "brainfuck": 0, "lisp": 262, "toml": 208, "yaml": 96, "css": 305,
       "sql": 158, "javascript": 52, "java": 36, "c": 222, "cpp": 200,
       "go": 172, "csharp": 148, "rust": 22, "haskell": 254, "fortran": 188,
       "pascal": 335, "lua": 230, "bash": 118, "generic": 215}
for _l in LANGS:
    _l.emoji = EMOJI.get(_l.key, "•")
    _l.hue = HUE.get(_l.key, 210)


# =========================================================================== #
# 5) pyflakes gate (Python only)
# =========================================================================== #
def pyflakes_report(src):
    try:
        from pyflakes.api import check
        from pyflakes.reporter import Reporter
    except Exception:
        return None
    warn, err = io.StringIO(), io.StringIO()
    try:
        check(src, "<generated>", Reporter(warn, err))
    except Exception as e:
        return f"pyflakes internal error: {e!r}"
    return warn.getvalue() + err.getvalue()


# =========================================================================== #
# 6) GUI helpers: colours, highlighter, custom widgets, visual scanner
# =========================================================================== #
def _human(x):
    try:
        xf = float(x)
    except (OverflowError, ValueError):
        return str(x)
    if xf < 10_000_000: return f"{int(x):,}"
    if xf < 1e12:       return f"{xf / 1e6:,.1f}M"
    return f"{xf:.2e}"

def A(h, s, l, a=255):
    """QColor from hue 0-359, sat/light 0-1 (Qt wants 0-255)."""
    c = QColor.fromHsl(int(h) % 360, int(s * 255), int(l * 255), a)
    return c

HL_DARK = {"kw": "#569cd6", "str": "#ce9178", "com": "#6a9955",
           "num": "#b5cea8", "tag": "#4ec9b0"}
HL_LIGHT = {"kw": "#0033b3", "str": "#067d17", "com": "#8c8c8c",
            "num": "#1750eb", "tag": "#0033b3"}

def _kwci(words):
    return r"(?i)\b(?:" + "|".join(re.escape(w) for w in words) + r")\b"

_STD_S = (r'"(?:\\.|[^"\\\n])*"', r"'(?:\\.|[^'\\\n])*'")
_DBL_S = (r"'(?:[^'\n]|'')*'", r'"(?:[^"\n]|"")*"')

def _H(kw=(), line=(), multi=(), strs=_STD_S, extra=()):
    return {"kw": _kwci(kw) if kw else "", "line": list(line),
            "multi": list(multi), "strs": list(strs), "extra": list(extra)}

HIGHLIGHT = {
    "python": _H("def return if elif else for while in not and or import from as class "
                 "try except finally with lambda pass break continue global nonlocal "
                 "assert yield del raise is True False None async await match case print".split(),
                 line=(r"#[^\n]*",),
                 multi=((r'"""', r'"""', "str"), (r"'''", r"'''", "str"))),
    "json": _H(("true", "false", "null")),
    "xml": _H(strs=_STD_S, multi=((r"<!--", r"-->", "com"),),
              extra=((r"</?[A-Za-z][A-Za-z0-9:_-]*", "tag"),)),
    "html": _H(strs=_STD_S, multi=((r"<!--", r"-->", "com"),),
               extra=((r"</?[A-Za-z][A-Za-z0-9:_-]*", "tag"),)),
    "regex": _H(),
    "brainfuck": _H(strs=(), extra=((r"[+\-<>\[\].,]+", "kw"),)),
    "lisp": _H(("define lambda let if cond else begin quote car cdr cons "
                "define-syntax when unless").split(), line=(r";[^\n]*",)),
    "toml": _H(strs=(r'"[^"\n]*"', r"'[^'\n]*'"), line=(r"#[^\n]*",),
               extra=((r"\[[^\]\n]*\]", "tag"),)),
    "yaml": _H(line=(r"#[^\n]*",), extra=((r"[A-Za-z_][\w.\-]*(?=\s*:)", "tag"),)),
    "css": _H(multi=((r"/\*", r"\*/", "com"),),
              extra=((r"[A-Za-z-]+(?=\s*:)", "kw"), (r"#[0-9a-fA-F]{3,8}\b", "num"))),
    "sql": _H(("select from where insert into values update set delete create table "
               "drop alter join left right inner outer cross on group by order having "
               "limit offset and or not null as distinct union all primary key foreign "
               "references default unique check view index").split(),
              line=(r"--[^\n]*",), multi=((r"/\*", r"\*/", "com"),),
              strs=_DBL_S + (r"`[^`]*`",)),
    "javascript": _H(("var let const function return if else for while do switch case "
                      "default break continue new delete typeof instanceof in of class "
                      "extends super this null undefined true false async await try catch "
                      "finally throw yield import export from").split(),
                     line=(r"//[^\n]*",), multi=((r"/\*", r"\*/", "com"),),
                     strs=_STD_S + (r"`[^`]*`",)),
    "java": _H(("public private protected class interface enum static final void int "
                "long double float boolean char byte short var new return if else for "
                "while do switch case default break continue try catch finally throw "
                "throws true false null this super extends implements import package "
                "instanceof").split(),
               line=(r"//[^\n]*",), multi=((r"/\*", r"\*/", "com"),)),
    "c": _H(("auto break case char const continue default do double else enum extern "
             "float for goto if inline int long register restrict return short signed "
             "sizeof static struct switch typedef union unsigned void volatile while "
             "bool true false NULL size_t").split(),
            line=(r"//[^\n]*",), multi=((r"/\*", r"\*/", "com"),),
            extra=((r"#\s*(include|define|ifdef|ifndef|endif|pragma|if|else|elif)\b", "tag"),)),
    "cpp": _H(("auto break case catch class const constexpr continue default delete do "
               "double else enum explicit extern false float for friend goto if inline "
               "int long namespace new nullptr operator private protected public "
               "return short signed sizeof static struct switch template this throw "
               "true try typedef typename union unsigned using virtual void volatile "
               "while override final").split(),
              line=(r"//[^\n]*",), multi=((r"/\*", r"\*/", "com"),),
              extra=((r"#\s*(include|define|ifdef|ifndef|endif|pragma|if|else|elif)\b", "tag"),)),
    "csharp": _H(("using namespace class struct interface enum public private protected "
                  "internal static readonly void int long double float bool string char "
                  "var object new return if else for foreach while do switch case default "
                  "break continue try catch finally throw true false null this base "
                  "virtual override async await in out ref get set value").split(),
                 line=(r"//[^\n]*",), multi=((r"/\*", r"\*/", "com"),),
                 extra=((r'@"(?:[^"]|"")*"', "str"),)),
    "go": _H(("package import func var const type struct interface map chan go defer "
              "if else for range switch case default return break continue fallthrough "
              "select nil true false iota").split(),
             line=(r"//[^\n]*",), multi=((r"/\*", r"\*/", "com"),),
             strs=_STD_S + (r"`[^`]*`",)),
    "rust": _H(("fn let mut const static if else match loop while for in return struct "
                "enum trait impl use mod pub crate self super where async await move ref "
                "dyn unsafe type as break continue true false").split(),
               line=(r"//[^\n]*",), multi=((r"/\*", r"\*/", "com"),),
               extra=((r"r#*\"[^\"]*\"#*", "str"),)),
    "haskell": _H(("module import qualified where let in do case of if then else data "
                   "type newtype instance class deriving main otherwise").split(),
                  line=(r"--[^\n]*",), multi=((r"\{-", r"-\}", "com"),)),
    "fortran": _H(("program end subroutine function implicit none integer real character "
                   "logical complex double precision parameter dimension write read print "
                   "do if then else elseif select case where call return stop module use "
                   "contains type interface operator").split(),
                  line=(r"![^\n]*",), strs=_DBL_S),
    "pascal": _H(("program begin end var const type procedure function if then else "
                  "while do for to downto repeat until case of record array string "
                  "integer real boolean char writeln write readln read uses nil div mod "
                  "and or not").split(),
                 line=(r"//[^\n]*",),
                 multi=((r"\{", r"\}", "com"), (r"\(\*", r"\*\)", "com")),
                 strs=(r"'(?:[^'\n]|'')*'",)),
    "lua": _H(("function end local if then else elseif for while do return break repeat "
               "until and or not nil true false in goto").split(),
              line=(r"--[^\n]*",),
              multi=((r"--\[\[", r"\]\]", "com"), (r"\[\[", r"\]\]", "str"))),
    "bash": _H(("if then else elif fi for while do done case esac function in echo "
                "export local return set unset read shift source alias").split(),
               line=(r"#[^\n]*",), extra=((r"\$\{?\w+\}?", "tag"),)),
    "generic": _H(("if else for while return function struct class def end").split(),
                  line=(r"//[^\n]*",), multi=((r"/\*", r"\*/", "com"),)),
}


class PreviewHighlighter(QSyntaxHighlighter):
    def __init__(self, doc, key, dark):
        super().__init__(doc)
        c = HL_DARK if dark else HL_LIGHT
        def F(kind, italic=False, bold=False):
            f = QTextCharFormat()
            f.setForeground(QColor(c[kind]))
            if italic: f.setFontItalic(True)
            if bold:   f.setFontWeight(QFont.Weight.Bold)
            return f
        cfg = HIGHLIGHT.get(key, {})
        self.rules = []
        if cfg.get("kw"):
            self.rules.append((QRegularExpression(cfg["kw"]), F("kw", bold=True)))
        self.rules.append((QRegularExpression(
            r"\b\d[\d_]*(?:\.\d+)?(?:[eE][+-]?\d+)?\b"), F("num")))
        for rx in cfg.get("strs", ()):
            self.rules.append((QRegularExpression(rx), F("str")))
        for rx, kind in cfg.get("extra", ()):
            self.rules.append((QRegularExpression(rx), F(kind)))
        for rx in cfg.get("line", ()):
            self.rules.append((QRegularExpression(rx), F("com", italic=True)))
        self.multi = [(QRegularExpression(s), QRegularExpression(e),
                       F(kind, italic=(kind == "com")))
                      for s, e, kind in cfg.get("multi", ())]

    def highlightBlock(self, text):
        prev = self.previousBlockState()
        if prev is None or prev < 0:
            prev = 0
        for rx, f in self.rules:
            it = rx.globalMatch(text)
            while it.hasNext():
                m = it.next()
                self.setFormat(m.capturedStart(), m.capturedLength(), f)
        mask, n = prev, len(text)
        for idx, (srx, erx, f) in enumerate(self.multi):
            bit = 1 << idx
            inside = bool(prev & bit)
            pos = 0
            while pos < n:
                if inside:
                    m = erx.match(text, pos)
                    if m.hasMatch():
                        self.setFormat(pos, m.capturedEnd() - pos, f)
                        pos = m.capturedEnd()
                        inside = False
                        mask &= ~bit
                    else:
                        self.setFormat(pos, n - pos, f)
                        pos = n
                else:
                    m = srx.match(text, pos)
                    if not m.hasMatch():
                        break
                    s = m.capturedStart()
                    m2 = erx.match(text, m.capturedEnd())
                    if m2.hasMatch():
                        e = m2.capturedEnd()
                        self.setFormat(s, e - s, f)
                        pos = e
                    else:
                        self.setFormat(s, n - s, f)
                        pos = n
                        inside = True
                        mask |= bit
            if n == 0:
                mask = (mask | bit) if inside else (mask & ~bit)
        self.setCurrentBlockState(mask)


# ----------------------------------------------------------- small widgets --
class RateGraph(QWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.samples = []
        self.setMinimumHeight(58)
        self.setMaximumHeight(74)
        self.line_c, self.fill_c = QColor("#1b7e3c"), QColor(27, 126, 60, 34)

    def set_colors(self, line, fill):
        self.line_c, self.fill_c = QColor(line), QColor(fill)
        self.update()

    def add(self, t, rate):
        self.samples.append((t, rate))
        if len(self.samples) > 600:
            self.samples = self.samples[-600:]
        self.update()

    def clear(self):
        self.samples.clear()
        self.update()

    def paintEvent(self, _e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        pal = self.palette()
        p.fillRect(self.rect(), pal.base())
        w, h = self.width(), self.height()
        p.setPen(pal.mid().color())
        p.drawRect(0, 0, w - 1, h - 1)
        if len(self.samples) < 2:
            p.setPen(pal.placeholderText().color())
            p.drawText(self.rect(), Qt.AlignmentFlag.AlignCenter,
                       "throughput (checks/s)")
            return
        mx = max(r for _t, r in self.samples) or 1.0
        t0, t1 = self.samples[0][0], self.samples[-1][0]
        span = max(t1 - t0, 1e-9)
        pts = [QPointF(((t - t0) / span) * (w - 10) + 5,
                       h - 6 - (r / mx) * (h - 14)) for t, r in self.samples]
        poly = QPolygonF(pts)
        fill = QPolygonF(poly)
        fill << QPointF(pts[-1].x(), h - 6) << QPointF(pts[0].x(), h - 6)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QBrush(self.fill_c))
        p.drawPolygon(fill)
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(QPen(self.line_c, 1.6))
        p.drawPolyline(poly)
        p.setPen(pal.text().color())
        p.drawText(self.rect().adjusted(6, 3, -6, 0),
                   Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignTop,
                   f"{mx:,.0f} peak · {self.samples[-1][1]:,.0f} now")


class WorkBar(QWidget):
    """Stacked bar: how much of the search space was parsed vs pruned away."""
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setFixedHeight(20)
        self.est = self.checked = self.elim = 0
        self.c_parsed = QColor("#1b7e3c")
        self.c_pruned = QColor(120, 120, 120, 90)

    def set_colors(self, accent, muted):
        self.c_parsed = QColor(accent)
        self.c_pruned = QColor(muted.red(), muted.green(), muted.blue(), 80)
        self.update()

    def set_values(self, est, checked, elim):
        self.est, self.checked, self.elim = est, checked, elim
        self.update()

    def paintEvent(self, _e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        pal = self.palette()
        w, h = self.width(), self.height()
        p.setPen(pal.mid().color())
        p.setBrush(pal.base())
        p.drawRoundedRect(0, 0, w - 1, h - 1, 5, 5)
        if self.est > 0:
            fe = min(self.elim / self.est, 1.0)
            fc = min(self.checked / self.est, 1.0 - fe)
            if fe > 0:
                p.setPen(Qt.PenStyle.NoPen); p.setBrush(self.c_pruned)
                p.drawRoundedRect(1, 1, max(int(fe * (w - 2)), 3), h - 2, 4, 4)
            if fc > 0:
                p.setPen(Qt.PenStyle.NoPen); p.setBrush(self.c_parsed)
                p.drawRoundedRect(1, 1, max(int(fc * (w - 2)), 3), h - 2, 4, 4)
            txt = (f"parsed {fc * 100:.1f}% · pruned {fe * 100:.1f}% · "
                   f"space {_human(self.est)}")
        else:
            txt = "no run yet"
        p.setPen(pal.text().color())
        p.drawText(self.rect(), Qt.AlignmentFlag.AlignCenter, txt)


class StructureMap(QWidget):
    """Lexical region strip + bracket-depth sparkline for the selected result."""
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setFixedHeight(54)
        self.regions = None            # list[(s, e, kind)] or None
        self.prof = []
        self.ok = True
        self.why = ""
        self.msg = "select a result to see its lexical structure"
        self.c_str = self.c_com = self.c_accent = self.c_track = None
        self.c_good = self.c_bad = None

    def set_palette(self, good, bad, accent, accent2, com, track, mut):
        self.c_good, self.c_bad, self.c_accent = QColor(good), QColor(bad), QColor(accent)
        self.c_str = QColor(accent2)
        self.c_com = QColor(com)
        self.c_track = QColor(track)
        self.c_mut = QColor(mut)
        self.update()

    def set_result(self, regions, prof, ok, why):
        self.regions, self.prof, self.ok, self.why = regions, prof, ok, why
        self.msg = ""
        self.update()

    def set_message(self, msg):
        self.regions = None
        self.msg = msg
        self.update()

    def paintEvent(self, _e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        pal = self.palette()
        w, h = self.width(), self.height()
        p.fillRect(self.rect(), pal.base())
        p.setPen(pal.mid().color())
        p.drawRoundedRect(0, 0, w - 1, h - 1, 6, 6)
        if self.regions is None:
            p.setPen(self.c_mut if self.c_mut else pal.placeholderText().color())
            p.drawText(self.rect(), Qt.AlignmentFlag.AlignCenter, self.msg)
            return
        n = max(len(self.prof), 1)
        # --- region strip ---
        by, bh = 4, 10
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(self.c_track)
        p.drawRoundedRect(4, by, w - 8, bh, 3, 3)
        for (s, e, kind) in self.regions:
            if kind == "code":
                continue
            x0 = 4 + (s / n) * (w - 8)
            x1 = 4 + (e / n) * (w - 8)
            p.setBrush(self.c_str if kind == "str" else self.c_com)
            p.drawRect(QRectF := __import__("PySide6.QtCore", fromlist=["QRectF"]).QRectF(x0, by, max(x1 - x0, 1), bh))
        # --- depth sparkline ---
        sy0, sy1 = by + bh + 6, h - 6
        p.setPen(QPen(self.c_track, 1))
        p.drawLine(4, sy1, w - 4, sy1)
        maxd = max(max(self.prof, default=0), 1)
        pts = [QPointF(4 + (i / max(n - 1, 1)) * (w - 8),
                       sy1 - (d / maxd) * (sy1 - sy0 - 2))
               for i, d in enumerate(self.prof)]
        if len(pts) >= 2:
            p.setPen(QPen(self.c_accent, 1.4))
            p.drawPolyline(QPolygonF(pts))
        # --- badge ---
        badge = "scan: balanced ✓" if self.ok else f"scan: unbalanced — {self.why}"
        p.setPen(self.c_good if self.ok else self.c_bad)
        p.drawText(self.rect().adjusted(0, 2, -8, 0),
                   Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignTop, badge)


class HeatGrid(QWidget):
    """One tile per visible result; click to jump, hover for source."""
    MAX_CELLS = 4000
    clicked_index = Signal(int)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setMouseTracking(True)
        self.items = []                # [(src, starred)]
        self.hue = 210
        self.dark = False
        self.setMinimumHeight(120)

    def set_accent(self, hue, dark):
        self.hue, self.dark = hue, dark
        self.update()

    def set_items(self, items):
        self.items = list(items)
        self.update()

    def _cell(self, w, h, n):
        return max(6, min(18, int(math.sqrt(max(w * h, 1) / max(n, 1)))))

    def paintEvent(self, _e):
        p = QPainter(self)
        pal = self.palette()
        p.fillRect(self.rect(), pal.base())
        w, h = self.width(), self.height()
        n = len(self.items)
        if n == 0:
            p.setPen(pal.placeholderText().color())
            p.drawText(self.rect(), Qt.AlignmentFlag.AlignCenter,
                       "no results to visualize yet")
            return
        cell = self._cell(w - 8, h - 8, n)
        cols = max(1, (w - 8) // cell)
        rows = (min(n, self.MAX_CELLS) + cols - 1) // cols
        off_y = max(4, (h - rows * cell) // 2)
        p.setPen(Qt.PenStyle.NoPen)
        for i in range(min(n, self.MAX_CELLS)):
            src, starred = self.items[i]
            r, c = divmod(i, cols)
            x, y = 4 + c * cell, off_y + r * cell
            if starred:
                col = QColor(255, 193, 7, 210)
            else:
                hh = (self.hue + (hash(src) % 24) - 12) % 360
                col = A(hh, 0.55, 0.55 if self.dark else 0.46)
            p.setBrush(col)
            p.drawRoundedRect(x, y, cell - 1, cell - 1, 2, 2)
        p.setPen(pal.placeholderText().color())
        note = f"{n:,} results" + (f" (showing first {self.MAX_CELLS:,})"
                                   if n > self.MAX_CELLS else "")
        p.drawText(self.rect().adjusted(0, 2, -6, 0),
                   Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignTop, note)

    def _idx_at(self, pos):
        n = len(self.items)
        if not n:
            return -1
        w, h = self.width(), self.height()
        cell = self._cell(w - 8, h - 8, n)
        cols = max(1, (w - 8) // cell)
        rows = (min(n, self.MAX_CELLS) + cols - 1) // cols
        off_y = max(4, (h - rows * cell) // 2)
        c, r = (pos.x() - 4) // cell, (pos.y() - off_y) // cell
        if c < 0 or r < 0 or c >= cols:
            return -1
        i = int(r * cols + c)
        return i if 0 <= i < min(n, self.MAX_CELLS) else -1

    def mouseMoveEvent(self, e):
        i = self._idx_at(e.position().toPoint())
        self.setToolTip(self.items[i][0][:1200] if i >= 0 else "")

    def mousePressEvent(self, e):
        i = self._idx_at(e.position().toPoint())
        if i >= 0:
            self.clicked_index.emit(i)


class Toast(QLabel):
    def __init__(self, parent):
        super().__init__(parent)
        self.setObjectName("toast")
        self.hide()
        self._eff = QGraphicsOpacityEffect(self)
        self.setGraphicsEffect(self._eff)
        self._anim = QPropertyAnimation(self._eff, b"opacity", self)
        self._anim.setDuration(170)
        self._anim.setEasingCurve(QEasingCurve.Type.OutCubic)
        self._anim.finished.connect(self._anim_done)
        self._timer = QTimer(self)
        self._timer.setSingleShot(True)
        self._timer.timeout.connect(self._fade_out)
        self._mode = "in"

    def show_msg(self, text):
        self.setText(text)
        self.adjustSize()
        par = self.parentWidget()
        self.move(max(8, par.width() - self.width() - 26),
                  max(8, par.height() - self.height() - 54))
        self._mode = "in"
        self._anim.stop()
        self._anim.setStartValue(0.0); self._anim.setEndValue(1.0)
        self._eff.setOpacity(0.0)
        self.show(); self.raise_()
        self._anim.start()
        self._timer.start(1600)

    def _fade_out(self):
        self._mode = "out"
        self._anim.stop()
        self._anim.setStartValue(self._eff.opacity())
        self._anim.setEndValue(0.0)
        self._anim.start()

    def _anim_done(self):
        if self._mode == "out":
            self.hide()


# ------------------------------------------- deterministic visual scanner ---
def _scan_visual_generic(spec, src):
    """Cosmetic greedy scan for the structure map. NOT used for validation."""
    n = len(src)
    strs = sorted([d for d in spec.strings if not d.raw], key=lambda d: -len(d.o))
    rust = next((d for d in spec.strings if d.raw == "rust"), None)
    cpp = next((d for d in spec.strings if d.raw == "cpp"), None)
    bcs = sorted(spec.bcomments, key=lambda b: -len(b.o))
    lcs = sorted(spec.lcomments, key=lambda s: -len(s))
    depths = [0] * len(spec.brackets)
    prof = [0] * n
    regions = []
    i, ok, why = 0, True, ""

    def dp(): return sum(depths)

    def mark(a, b, kind):
        regions.append((a, b, kind))
        for p in range(a, b):
            prof[p] = dp()

    while i < n:
        ch = src[i]
        matched = False
        if rust and ch == "r":
            j = i + 1
            while j < n and src[j] == "#":
                j += 1
            if j < n and src[j] == '"':
                closer = '"' + src[i + 1:j]
                k = src.find(closer, j + 1)
                end = n if k < 0 else k + len(closer)
                if k < 0:
                    ok, why = False, "raw string unterminated"
                mark(i, end, "str"); i = end; matched = True
        if not matched and cpp and src.startswith(cpp.o, i):
            j = i + len(cpp.o)
            k = j
            while k < n and src[k] not in "()":
                if src[k] in ' \\\t\r\n"':
                    break
                k += 1
            if k < n and src[k] == "(" and len(src[j:k]) <= 16:
                closer = ")" + src[j:k] + '"'
                p2 = src.find(closer, k + 1)
                end = n if p2 < 0 else p2 + len(closer)
                if p2 < 0:
                    ok, why = False, "raw string unterminated"
                mark(i, end, "str"); i = end
            else:
                ok, why = False, "bad raw-string delimiter"
                mark(i, n, "str"); i = n
            matched = True
        if not matched:
            for d in strs:
                if src.startswith(d.o, i):
                    j = i + len(d.o); closed = False
                    while j < n:
                        if d.esc and src[j] == "\\":
                            j += 2; continue
                        if d.dbl and src.startswith(d.c, j):
                            if src.startswith(d.c + d.c, j):
                                j += 2; continue
                            j += len(d.c); closed = True; break
                        if src.startswith(d.c, j):
                            j += len(d.c); closed = True; break
                        if src[j] == "\n" and not d.nl:
                            break
                        j += 1
                    if not closed:
                        ok, why = False, "string unterminated"
                    mark(i, min(j, n), "str"); i = min(j, n)
                    matched = True; break
        if not matched:
            for bc in bcs:
                if src.startswith(bc.o, i):
                    j = i + len(bc.o); nest = 1
                    while j < n and nest > 0:
                        if bc.nested and src.startswith(bc.o, j):
                            nest += 1; j += len(bc.o); continue
                        if src.startswith(bc.c, j):
                            nest -= 1; j += len(bc.c); continue
                        j += 1
                    if nest > 0:
                        ok, why = False, "block comment unterminated"
                    mark(i, min(j, n), "bcom"); i = min(j, n)
                    matched = True; break
        if not matched:
            for lc in lcs:
                if src.startswith(lc, i):
                    j = src.find("\n", i)
                    end = n if j < 0 else j
                    mark(i, end, "lcom"); i = end
                    matched = True; break
        if not matched:
            prof[i] = dp()
            for bi, (o, c) in enumerate(spec.brackets):
                if ch == o:
                    depths[bi] += 1
                    break
                if ch == c:
                    if depths[bi] > 0:
                        depths[bi] -= 1
                    else:
                        ok, why = False, "unmatched closing bracket"
                    break
            i += 1
            if spec.cont and ch == spec.cont and i < n and src[i] == "\n":
                prof[i] = prof[i - 1]
                i += 1
    merged = []
    for r in regions:
        if merged and merged[-1][2] == r[2] and merged[-1][1] == r[0]:
            merged[-1] = (merged[-1][0], r[1], r[2])
        else:
            merged.append(r)
    return merged, prof, ok, why


class ResultsList(QListWidget):
    star_changed = Signal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        self.setUniformItemSizes(True)
        self.setAlternatingRowColors(True)
        self.hint = ("No results yet.\n"
                     "Press Ctrl+⏎ to start — candidates are parsed, never executed.")
        self.viewport().installEventFilter(self)

    @staticmethod
    def _disp(src):
        d = src.replace("\n", "⏎").replace("\t", "⇥")
        return (d[:200] + " …") if len(d) > 200 else d

    def toggle_star(self, it):
        star = not it.data(Qt.ItemDataRole.UserRole + 1)
        it.setData(Qt.ItemDataRole.UserRole + 1, star)
        it.setText(("★ " if star else "") +
                   self._disp(it.data(Qt.ItemDataRole.UserRole)))
        it.setBackground(QBrush(QColor(255, 193, 7, 80)) if star else QBrush())
        self.star_changed.emit()

    def eventFilter(self, obj, ev):
        if obj is self.viewport() and ev.type() == QEvent.Type.Paint \
                and self.count() == 0 and self.hint:
            p = QPainter(self.viewport())
            p.setPen(self.palette().placeholderText().color())
            p.drawText(self.viewport().rect(),
                       Qt.AlignmentFlag.AlignCenter | Qt.TextFlag.TextWordWrap,
                       self.hint)
            return True
        return super().eventFilter(obj, ev)

    def keyPressEvent(self, e):
        if e.key() in (Qt.Key.Key_S, Qt.Key.Key_Asterisk):
            it = self.currentItem()
            if it is not None:
                self.toggle_star(it)
                return
        super().keyPressEvent(e)


SHORTCUTS_TEXT = (
    "Ctrl+Return    Start enumeration\n"
    "Ctrl+P         Pause / resume\n"
    "Esc            Stop\n"
    "Ctrl+F         Focus results filter\n"
    "Ctrl+G         Toggle overview heat grid\n"
    "Ctrl+S         Export visible results…\n"
    "Ctrl+Shift+S   Export ★ starred…\n"
    "Ctrl+Shift+C   Copy all (filtered)\n"
    "S  or  *       Star/unstar selected result (list focused)\n"
    "Ctrl+T         Toggle dark theme\n"
    "Ctrl+U         Toggle scratchpad validator\n"
    "Ctrl+= / Ctrl+- / Ctrl+0    Zoom in / out / reset\n"
    "Ctrl+Q         Quit")


# =========================================================================== #
# 7) Worker thread
# =========================================================================== #
class Enumerator(QThread):
    found_batch = Signal(list)
    stats = Signal(dict)
    progress = Signal(int)
    finished_run = Signal(str)

    def __init__(self, cfg):
        super().__init__()
        self.cfg = cfg
        self.lang = LANG_BY_KEY[cfg["lang"]]
        self._cancel = False
        self._paused = False
        self._checked = self._pruned = self._elim = self._valid = 0
        self._est = 0
        self._batch = []
        self._last = self._t0 = 0.0
        self._reason = "complete"
        self._machine = None

    def cancel(self): self._cancel = True
    def pause(self):  self._paused = True
    def resume(self): self._paused = False

    def _gate(self):
        while self._paused and not self._cancel:
            time.sleep(0.05)

    def _tick(self, force=False):
        now = time.perf_counter()
        if force or (now - self._last) >= 0.15:
            self._last = now
            self.stats.emit(dict(checked=self._checked, pruned=self._pruned,
                                 valid=self._valid, elim=self._elim,
                                 est=self._est, elapsed=now - self._t0))
            if self._batch:
                self.found_batch.emit(self._batch); self._batch = []
            frac = min((self._checked + self._elim) / max(self._est, 1), 1.0)
            self.progress.emit(int(frac * 1000))

    def _accept(self, src):
        self._checked += 1
        ok, _msgs = self.lang.validate(src)
        if ok and self.lang.pyflakes and self.cfg.get("use_pyflakes"):
            out = pyflakes_report(src)
            if out is None:
                pass
            elif out.strip() and self.cfg.get("strict", False):
                ok = False
        if ok:
            self._valid += 1
            self._batch.append(src)
            return self._valid < self.cfg.get("max_results", 10_000)
        return True

    def run(self):
        self._t0 = time.perf_counter()
        self._machine = self.lang.make_machine()
        try:
            if self.cfg["mode"] == "chars":
                self._run_chars()
            else:
                self._run_tokens()
        except Exception as e:
            self._reason = f"error: {e!r}"
        self._tick(force=True)
        if self._batch:
            self.found_batch.emit(self._batch); self._batch = []
        if self._cancel:
            msg = "Stopped by user."
        elif self._reason == "cap":
            msg = "Stopped: result cap reached."
        else:
            msg = self._reason if self._reason.startswith("error") \
                else "Search space exhausted."
        self.finished_run.emit(msg)

    def _run_chars(self):
        cfg = self.cfg
        n, alpha = cfg["n"], sorted(set(cfg["alphabet"]))
        k, have = len(alpha), set(alpha)
        self._est = k ** n
        m = self._machine

        if m is None:
            for tup in itertools.product(alpha, repeat=n):
                self._gate()
                if self._cancel: return
                if not self._accept("".join(tup)):
                    self._reason = "cap"; return
                self._tick()
            return

        stack = []
        for ch in reversed(alpha):
            S = m.step(m.init(), ch)
            if S and m.completable(S, n - 1, have):
                stack.append((ch, S))
            else:
                self._pruned += 1; self._elim += k ** (n - 1)

        while stack:
            self._gate()
            if self._cancel: return
            prefix, S = stack.pop()
            if len(prefix) == n:
                if m.acceptable(S):
                    if not self._accept(prefix):
                        self._reason = "cap"; return
                else:
                    self._pruned += 1; self._elim += 1
                self._tick()
            else:
                rem = n - len(prefix) - 1
                for ch in reversed(alpha):
                    S2 = m.step(S, ch)
                    if S2 and m.completable(S2, rem, have):
                        stack.append((prefix + ch, S2))
                    else:
                        self._pruned += 1; self._elim += k ** rem
                self._tick()

    def _prefix_dead(self, joined):
        m, cfg = self._machine, self.cfg
        if m is None or not cfg.get("aggressive", True):
            return False
        S = m.init()
        for ch in joined:
            S = m.step(S, ch)
            if not S:
                return True
        return False

    def _run_tokens(self):
        cfg = self.cfg
        toks, n, sep = cfg["tokens"], cfg["n"], cfg["sep"]
        k = len(toks)
        self._est = k ** n
        stack = []
        for t in reversed(toks):
            if n > 1 and self._prefix_dead(t):
                self._pruned += 1; self._elim += k ** (n - 1)
                continue
            stack.append((t, 1))
        while stack:
            self._gate()
            if self._cancel: return
            joined, cnt = stack.pop()
            if cnt == n:
                if not self._accept(joined):
                    self._reason = "cap"; return
                self._tick()
            else:
                rem_after = n - cnt - 1
                for t in reversed(toks):
                    j2 = joined + sep + t
                    if self._prefix_dead(j2):
                        self._pruned += 1; self._elim += k ** rem_after
                        continue
                    stack.append((j2, cnt + 1))
                self._tick()


# =========================================================================== #
# 8) Main window
# =========================================================================== #
def _eta(sec):
    if sec is None or sec != sec or sec == float("inf"):
        return "—"
    s = int(sec)
    if s < 60:      return f"{s}s"
    if s < 3600:    return f"{s // 60}m {s % 60:02d}s"
    h = s / 3600
    if h < 72:      return f"{h:.1f}h"
    return f"{h / 24:.1f}d"


SPIN_FRAMES = "⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏"


class MainWindow(QMainWindow):
    S = QSettings("staticenum", "ProgramEnumerator")

    def __init__(self):
        super().__init__()
        self._base_title = ("Program Enumerator — static validation only "
                            "(candidates are never executed)")
        self.setWindowTitle(self._base_title)
        self.resize(1220, 820)
        self.worker = None
        self._t0 = None
        self._found_total = self._visible = 0
        self._capped = False
        self._hl = None
        self._hl_lang = None
        self.dark = False
        self._last_dir = ""
        self._restoring = False
        self._restored_alpha = False
        self._vis_items = []
        self._build_ui()
        self._restore_settings()
        if self.preset.count() == 0:
            self._on_lang()
        self._restoring = False
        if not self._restored_alpha:
            self._apply_preset(0)
        self._update_space()
        self._apply_style()

    # ------------------------------------------------------------- theming --
    def _apply_style(self):
        """Rebuild palette + QSS from theme and the current language accent."""
        app = QApplication.instance()
        app.setStyle("Fusion")
        hue = self._cur_lang().hue if self.lang_combo.count() else 210
        accent   = A(hue, 0.62, 0.58 if self.dark else 0.38)
        accent2  = A(hue, 0.70, 0.66 if self.dark else 0.46)
        accent_t = "#10141a" if self.dark else "#ffffff"
        if self.dark:
            win, field, tile = "#23272e", "#2b3037", "#2b3037"
            border, text, mut = "#3a4048", "#d8dde3", "#8b929a"
            alt, btn, btn_hov = "#30353d", "#333a42", "#3d444d"
            good, bad, com_c = "#4caf50", "#e06c60", "#6a9955"
            pal = QPalette()
            pal.setColor(QPalette.ColorRole.Window, QColor(53, 53, 53))
            pal.setColor(QPalette.ColorRole.WindowText, QColor(220, 220, 220))
            pal.setColor(QPalette.ColorRole.Base, QColor(35, 35, 35))
            pal.setColor(QPalette.ColorRole.AlternateBase, QColor(45, 45, 45))
            pal.setColor(QPalette.ColorRole.ToolTipBase, QColor(45, 45, 45))
            pal.setColor(QPalette.ColorRole.ToolTipText, QColor(220, 220, 220))
            pal.setColor(QPalette.ColorRole.Text, QColor(220, 220, 220))
            pal.setColor(QPalette.ColorRole.Button, QColor(53, 53, 53))
            pal.setColor(QPalette.ColorRole.ButtonText, QColor(220, 220, 220))
            pal.setColor(QPalette.ColorRole.BrightText, Qt.GlobalColor.red)
            pal.setColor(QPalette.ColorRole.Highlight, accent)
            pal.setColor(QPalette.ColorRole.HighlightedText, Qt.GlobalColor.white)
            pal.setColor(QPalette.ColorGroup.Disabled, QPalette.ColorRole.Text,
                         QColor(120, 120, 120))
            pal.setColor(QPalette.ColorGroup.Disabled, QPalette.ColorRole.ButtonText,
                         QColor(120, 120, 120))
        else:
            win, field, tile = "#f5f6f8", "#ffffff", "#ffffff"
            border, text, mut = "#d7dbe0", "#1d2126", "#6a7178"
            alt, btn, btn_hov = "#eef0f3", "#e8eaee", "#dde1e6"
            good, bad, com_c = "#1b7e3c", "#c0392b", "#3f7f4f"
            pal = app.style().standardPalette()
        app.setPalette(pal)
        qss = f"""
        QWidget {{ color: {text}; font-size: 10pt; }}
        QLabel#muted {{ color: {mut}; }}
        QFrame#tile {{ background: {tile}; border: 1px solid {border};
                       border-radius: 8px; }}
        QLabel#tile_val {{ font-size: 14pt; font-weight: 600; }}
        QLabel#tile_cap {{ color: {mut}; font-size: 8pt; }}
        QLabel#pill {{ border-radius: 10px; padding: 2px 10px; font-weight: 600; }}
        QPushButton {{ background: {btn}; border: 1px solid {border};
                       border-radius: 6px; padding: 5px 12px; }}
        QPushButton:hover {{ background: {btn_hov}; }}
        QPushButton:disabled {{ color: {mut}; }}
        QPushButton#primary {{ background: {accent.name()}; color: {accent_t};
                               border: none; font-weight: 600; }}
        QPushButton#primary:hover {{ background: {accent2.name()}; }}
        QPushButton#small {{ padding: 2px 8px; font-size: 9pt; }}
        QLineEdit, QPlainTextEdit, QSpinBox, QComboBox {{
            background: {field}; border: 1px solid {border};
            border-radius: 6px; padding: 3px 6px;
            selection-background-color: {accent.name()}; }}
        QComboBox::drop-down {{ border: none; width: 18px; }}
        QComboBox QAbstractItemView {{ background: {field};
            border: 1px solid {border};
            selection-background-color: {accent.name()}; }}
        QProgressBar {{ background: {field}; border: 1px solid {border};
                        border-radius: 6px; text-align: center; height: 16px; }}
        QProgressBar::chunk {{ border-radius: 5px; background:
            qlineargradient(x1:0,y1:0,x2:1,y2:0,
                stop:0 {accent.name()}, stop:1 {accent2.name()}); }}
        QListWidget {{ background: {field}; border: 1px solid {border};
                       border-radius: 6px; alternate-background-color: {alt}; }}
        QListWidget::item {{ padding: 2px 4px; }}
        QListWidget::item:selected {{ background: {accent.name()};
                                      color: {accent_t}; }}
        QDockWidget::title {{ background: {tile}; border: 1px solid {border};
                              padding: 4px 8px; }}
        QSplitter::handle {{ background: {border}; }}
        QToolTip {{ background: {field}; color: {text};
                    border: 1px solid {border}; padding: 4px; }}
        QMenu {{ background: {field}; border: 1px solid {border}; }}
        QMenu::item:selected {{ background: {accent.name()}; color: {accent_t}; }}
        QLabel#toast {{ background: rgba(30,34,40,235); color: #f2f4f6;
                        border: 1px solid {border}; border-radius: 10px;
                        padding: 8px 14px; }}
        """
        app.setStyleSheet(qss)
        self.graph.set_colors(accent.name(), QColor(accent.red(), accent.green(),
                                                    accent.blue(), 40))
        self.workbar.set_colors(accent, QColor(mut))
        self.sm.set_palette(good, bad, accent.name(), accent2.name(), com_c,
                            field, QColor(mut))
        self.heat.set_accent(hue, self.dark)
        self._refresh_highlighter()

    # ------------------------------------------------------------------ UI --
    def _build_ui(self):
        central = QWidget(); self.setCentralWidget(central)
        root = QVBoxLayout(central)

        grid = QGridLayout()
        grid.addWidget(QLabel("Language:"), 0, 0)
        self.lang_combo = QComboBox()
        for l in LANGS:
            self.lang_combo.addItem(f"{l.emoji}  {l.name}"
                                    + ("" if l.available else "  ✗"), l.key)
        grid.addWidget(self.lang_combo, 0, 1)
        grid.addWidget(QLabel("Preset:"), 0, 2)
        self.preset = QComboBox(); grid.addWidget(self.preset, 0, 3)
        grid.addWidget(QLabel("Length n:"), 0, 4)
        self.n_spin = QSpinBox(); self.n_spin.setRange(1, 24); self.n_spin.setValue(4)
        grid.addWidget(self.n_spin, 0, 5)

        grid.addWidget(QLabel("Mode:"), 1, 0)
        self.mode = QComboBox(); self.mode.addItems(["Characters", "Tokens"])
        grid.addWidget(self.mode, 1, 1)
        grid.addWidget(QLabel("Token joiner:"), 1, 2)
        self.sep = QComboBox(); self.sep.addItems(["none", "space"])
        grid.addWidget(self.sep, 1, 3)
        self.chk_py = QCheckBox("pyflakes gate"); self.chk_py.setEnabled(HAS_PYFLAKES)
        if not HAS_PYFLAKES:
            self.chk_py.setToolTip("pip install pyflakes to enable")
        grid.addWidget(self.chk_py, 1, 4)
        self.chk_strict = QCheckBox("…strict"); self.chk_strict.setEnabled(False)
        self.chk_py.toggled.connect(self.chk_strict.setEnabled)
        grid.addWidget(self.chk_strict, 1, 5)

        self.chk_agg = QCheckBox("aggressive prefix pruning (tokens)")
        self.chk_agg.setChecked(True)
        grid.addWidget(self.chk_agg, 2, 0, 1, 2)
        grid.addWidget(QLabel("Stop after"), 2, 2)
        self.max_results = QSpinBox()
        self.max_results.setRange(1, 100_000); self.max_results.setValue(10_000)
        grid.addWidget(self.max_results, 2, 3)
        self.space_lbl = QLabel(""); grid.addWidget(self.space_lbl, 2, 4, 1, 2)
        root.addLayout(grid)

        self.engine_lbl = QLabel(); self.engine_lbl.setTextFormat(Qt.TextFormat.RichText)
        self.engine_lbl.setWordWrap(True)
        self.engine_lbl.setObjectName("muted")
        root.addWidget(self.engine_lbl)

        mono = QFontDatabase.systemFont(QFontDatabase.SystemFont.FixedFont)
        self.mono_family = mono.family()
        pt = mono.pointSize()
        self.font_pt = pt if pt and pt > 0 else 10
        self.alphabet_edit = QPlainTextEdit(); self.alphabet_edit.setFixedHeight(64)
        self.alphabet_edit.textChanged.connect(self._update_alpha_info)
        root.addWidget(self.alphabet_edit)

        btns = QHBoxLayout()
        self.start_btn = QPushButton("▶  Start enumeration   (Ctrl+⏎)")
        self.start_btn.setObjectName("primary")
        self.start_btn.clicked.connect(self._start)
        self.pause_btn = QPushButton("⏸ Pause"); self.pause_btn.setEnabled(False)
        self.pause_btn.clicked.connect(self._toggle_pause)
        self.stop_btn = QPushButton("■ Stop  (Esc)"); self.stop_btn.setEnabled(False)
        self.stop_btn.clicked.connect(self._stop)
        self.spin_lbl = QLabel(""); self.spin_lbl.setVisible(False)
        self.spin_lbl.setStyleSheet("font-size:14pt; font-weight:700;")
        self.spin_timer = QTimer(self); self.spin_timer.setInterval(120)
        self._spin_i = 0
        self.spin_timer.timeout.connect(self._spin_tick)
        btns.addWidget(self.start_btn); btns.addWidget(self.pause_btn)
        btns.addWidget(self.stop_btn); btns.addWidget(self.spin_lbl)
        btns.addStretch(1)
        root.addLayout(btns)

        self.progress = QProgressBar(); self.progress.setRange(0, 1000)
        self.progress.setFormat("%p%")
        root.addWidget(self.progress)
        self.workbar = WorkBar(); root.addWidget(self.workbar)
        root.addLayout(self._build_tiles())
        self.graph = RateGraph(); root.addWidget(self.graph)

        frow = QHBoxLayout()
        frow.addWidget(QLabel("Filter:"))
        self.filter_edit = QLineEdit()
        self.filter_edit.setPlaceholderText("substring filter…  (Ctrl+F)")
        self.filter_edit.setClearButtonEnabled(True)
        self.filter_timer = QTimer(self)
        self.filter_timer.setSingleShot(True); self.filter_timer.setInterval(180)
        self.filter_timer.timeout.connect(self._apply_filter)
        self.filter_edit.textChanged.connect(self.filter_timer.start)
        self.chk_star = QCheckBox("★ only")
        self.chk_star.toggled.connect(lambda _c: self._apply_filter())
        frow.addWidget(self.filter_edit, 1); frow.addWidget(self.chk_star)
        root.addLayout(frow)

        self.results_title = QLabel("Valid programs: 0")
        self.results_title.setTextFormat(Qt.TextFormat.RichText)
        root.addWidget(self.results_title)

        split = QSplitter()
        self.results = ResultsList()
        self.results.itemSelectionChanged.connect(self._show_preview)
        self.results.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.results.customContextMenuRequested.connect(self._results_menu)
        self.results.star_changed.connect(lambda: self._apply_filter())

        right = QWidget(); rv = QVBoxLayout(right)
        rv.setContentsMargins(0, 0, 0, 0); rv.setSpacing(4)
        chips = QHBoxLayout()
        self.chip_status = QLabel("—"); self.chip_status.setObjectName("pill")
        self.chip_engine = QLabel(""); self.chip_engine.setObjectName("pill")
        self._set_chip(self.chip_engine, "", None)
        self.chip_copy = QPushButton("Copy"); self.chip_copy.setObjectName("small")
        self.chip_star = QPushButton("★ Star"); self.chip_star.setObjectName("small")
        self.chip_copy.clicked.connect(self._copy_selected)
        self.chip_star.clicked.connect(self._star_current)
        chips.addWidget(self.chip_status); chips.addWidget(self.chip_engine)
        chips.addStretch(1); chips.addWidget(self.chip_copy)
        chips.addWidget(self.chip_star)
        rv.addLayout(chips)
        self.sm = StructureMap(); rv.addWidget(self.sm)
        self.preview = QPlainTextEdit(); self.preview.setReadOnly(True)
        self.preview.setLineWrapMode(QPlainTextEdit.LineWrapMode.NoWrap)
        rv.addWidget(self.preview, 1)
        split.addWidget(self.results); split.addWidget(right)
        split.setSizes([520, 640])
        root.addWidget(split, 1)

        copy_row = QHBoxLayout()
        cp = QPushButton("Copy selected"); cp.clicked.connect(self._copy_selected)
        copy_row.addWidget(cp); copy_row.addStretch(1)
        root.addLayout(copy_row)

        note = QLabel("Static validation only — candidates go through the selected "
                      "language's parser/linter and are never executed (no exec/eval/run anywhere).")
        note.setObjectName("muted")
        root.addWidget(note)

        self._build_scratch()
        self._build_overview()
        self._build_menus()
        self.toast = Toast(self)

        self.lang_combo.currentIndexChanged.connect(self._on_lang)
        self.mode.currentIndexChanged.connect(self._on_mode)
        self.preset.currentIndexChanged.connect(self._on_preset)
        self.n_spin.valueChanged.connect(self._update_space)
        self._apply_fonts()

    def _build_tiles(self):
        row = QHBoxLayout(); row.setSpacing(6)
        self.tiles = {}
        specs = [("valid", "VALID"), ("checked", "VALIDATED"),
                 ("pruned", "PRUNED"), ("elim", "ELIMINATED"),
                 ("rate", "RATE"), ("eta", "ETA")]
        for key, cap in specs:
            fr = QFrame(); fr.setObjectName("tile")
            fr.setMinimumHeight(50)
            v = QVBoxLayout(fr); v.setContentsMargins(10, 4, 10, 4); v.setSpacing(0)
            val = QLabel("—"); val.setObjectName("tile_val")
            val.setAlignment(Qt.AlignmentFlag.AlignCenter)
            capl = QLabel(cap); capl.setObjectName("tile_cap")
            capl.setAlignment(Qt.AlignmentFlag.AlignCenter)
            v.addWidget(val); v.addWidget(capl)
            row.addWidget(fr, 1)
            self.tiles[key] = val
        self._tile_colors = {}
        return row

    def _tile_colorize(self, good, bad, mut, accent, accent2):
        colors = {"valid": good, "checked": accent, "pruned": "#c98a2b",
                  "elim": mut, "rate": accent2, "eta": None}
        self._tile_colors = colors
        for key, lbl in self.tiles.items():
            c = colors.get(key)
            lbl.setStyleSheet(f"color:{c};" if c else "")

    def _spin_tick(self):
        self._spin_i = (self._spin_i + 1) % len(SPIN_FRAMES)
        self.spin_lbl.setText(SPIN_FRAMES[self._spin_i])

    def _build_scratch(self):
        w = QWidget(); v = QVBoxLayout(w); v.setContentsMargins(4, 4, 4, 4)
        self.scratch = QPlainTextEdit()
        self.scratch.setPlaceholderText(
            "Paste any snippet here and validate it statically against the current language…")
        self.scratch.setMaximumHeight(110)
        h = QHBoxLayout()
        self.scratch_btn = QPushButton("Validate snippet")
        self.scratch_btn.clicked.connect(self._validate_scratch)
        h.addWidget(self.scratch_btn); h.addStretch(1)
        self.scratch_out = QPlainTextEdit(); self.scratch_out.setReadOnly(True)
        self.scratch_out.setMaximumHeight(96)
        v.addWidget(self.scratch); v.addLayout(h); v.addWidget(self.scratch_out)
        self.scratch_dock = QDockWidget("Scratchpad validator", self)
        self.scratch_dock.setWidget(w)
        self.scratch_dock.setFeatures(
            QDockWidget.DockWidgetFeature.DockWidgetClosable |
            QDockWidget.DockWidgetFeature.DockWidgetMovable)
        self.addDockWidget(Qt.DockWidgetArea.BottomDockWidgetArea, self.scratch_dock)
        self.scratch_dock.hide()

    def _build_overview(self):
        self.heat = HeatGrid()
        self.heat.clicked_index.connect(self._heat_jump)
        self.heat_dock = QDockWidget("Overview — heat grid", self)
        self.heat_dock.setWidget(self.heat)
        self.heat_dock.setFeatures(
            QDockWidget.DockWidgetFeature.DockWidgetClosable |
            QDockWidget.DockWidgetFeature.DockWidgetMovable)
        self.addDockWidget(Qt.DockWidgetArea.RightDockWidgetArea, self.heat_dock)
        self.heat_dock.hide()
        self._ov_timer = QTimer(self)
        self._ov_timer.setSingleShot(True); self._ov_timer.setInterval(220)
        self._ov_timer.timeout.connect(self._rebuild_overview)

    def _schedule_overview(self):
        self._ov_timer.start()

    def _rebuild_overview(self):
        items, self._vis_items = [], []
        for i in range(self.results.count()):
            it = self.results.item(i)
            if it.isHidden():
                continue
            items.append((it.data(Qt.ItemDataRole.UserRole),
                          bool(it.data(Qt.ItemDataRole.UserRole + 1))))
            self._vis_items.append(it)
        self.heat.set_items(items)

    def _heat_jump(self, idx):
        if 0 <= idx < len(self._vis_items):
            it = self._vis_items[idx]
            self.results.setCurrentItem(it)
            self.results.scrollToItem(it)

    def _build_menus(self):
        mb = self.menuBar()
        m_file = mb.addMenu("&File")
        self._act(m_file, "Export visible results…", "Ctrl+S", lambda: self._export(False))
        self._act(m_file, "Export ★ starred…", "Ctrl+Shift+S", lambda: self._export(True))
        self._act(m_file, "Copy all (filtered)", "Ctrl+Shift+C", self._copy_all)
        m_file.addSeparator()
        self._act(m_file, "Clear results", None, self._clear_results)
        m_file.addSeparator()
        self._act(m_file, "Quit", "Ctrl+Q", self.close)

        m_run = mb.addMenu("&Run")
        self._act(m_run, "Start enumeration", "Ctrl+Return", self._start)
        self.a_pause = QAction("Pause", self)
        self.a_pause.setShortcut(QKeySequence("Ctrl+P"))
        self.a_pause.triggered.connect(self._toggle_pause)
        self.a_pause.setEnabled(False)
        m_run.addAction(self.a_pause)
        self._act(m_run, "Stop", "Esc", self._stop)

        m_view = mb.addMenu("&View")
        self.theme_act = QAction("Dark theme", self)
        self.theme_act.setCheckable(True)
        self.theme_act.setShortcut(QKeySequence("Ctrl+T"))
        self.theme_act.toggled.connect(self._set_theme)
        m_view.addAction(self.theme_act)
        m_view.addSeparator()
        ov = self.heat_dock.toggleViewAction()
        ov.setText("Overview heat grid")
        ov.setShortcut(QKeySequence("Ctrl+G"))
        m_view.addAction(ov)
        tva = self.scratch_dock.toggleViewAction()
        tva.setText("Scratchpad validator")
        tva.setShortcut(QKeySequence("Ctrl+U"))
        m_view.addAction(tva)
        m_view.addSeparator()
        zi = QAction("Zoom in", self)
        zi.setShortcut(QKeySequence(QKeySequence.StandardKey.ZoomIn))
        zi.triggered.connect(lambda: self._zoom(+1)); m_view.addAction(zi)
        zo = QAction("Zoom out", self)
        zo.setShortcut(QKeySequence(QKeySequence.StandardKey.ZoomOut))
        zo.triggered.connect(lambda: self._zoom(-1)); m_view.addAction(zo)
        zr = QAction("Reset zoom", self); zr.setShortcut(QKeySequence("Ctrl+0"))
        zr.triggered.connect(lambda: self._zoom(0)); m_view.addAction(zr)
        self._act(m_view, "Focus results filter", "Ctrl+F", self.filter_edit.setFocus)

        m_help = mb.addMenu("&Help")
        self._act(m_help, "Engine status…", None, self._engine_report)
        self._act(m_help, "Keyboard shortcuts…", None, self._shortcuts_dlg)
        self._act(m_help, "About…", None, self._about)

    def _act(self, menu, text, key, slot):
        a = QAction(text, self)
        if key: a.setShortcut(QKeySequence(key))
        a.triggered.connect(slot)
        menu.addAction(a)
        return a

    # ------------------------------------------------- fonts / zoom / theme --
    def _apply_fonts(self):
        f = QFont(self.mono_family); f.setPointSize(self.font_pt)
        for w in (self.results, self.preview, self.alphabet_edit,
                  self.scratch, self.scratch_out):
            w.setFont(f)

    def _zoom(self, d):
        self.font_pt = 10 if d == 0 else max(7, min(24, self.font_pt + d))
        self._apply_fonts()
        self.S.setValue("fontpt", self.font_pt)

    def _set_theme(self, dark):
        self.dark = bool(dark)
        self._apply_style()
        self.S.setValue("dark", self.dark)

    def _refresh_highlighter(self, key=None):
        if key is None:
            key = self.lang_combo.currentData() if self.lang_combo.count() else "python"
        if self._hl is not None:
            self._hl.setDocument(None)
            self._hl.deleteLater()
        self._hl = PreviewHighlighter(self.preview.document(), key or "python", self.dark)
        self._hl_lang = key

    def _restore_settings(self):
        s = self.S
        try:
            g = s.value("geometry")
            if g is not None: self.restoreGeometry(g)
            st = s.value("windowState")
            if st is not None: self.restoreState(st)
        except Exception:
            pass
        self.dark = s.value("dark", False, type=bool)
        self.theme_act.setChecked(self.dark)
        self.font_pt = s.value("fontpt", self.font_pt, type=int)
        self._apply_fonts()
        self._last_dir = s.value("lastdir", "", type=str)
        i = self.lang_combo.findData(s.value("lang", "python", type=str))
        if i >= 0: self.lang_combo.setCurrentIndex(i)
        self.mode.setCurrentIndex(s.value("mode", 0, type=int))
        self.n_spin.setValue(s.value("n", 4, type=int))
        self.sep.setCurrentIndex(s.value("sep", 0, type=int))
        self.chk_py.setChecked(s.value("pyflakes", False, type=bool))
        self.chk_strict.setChecked(s.value("strict", False, type=bool))
        self.chk_agg.setChecked(s.value("agg", True, type=bool))
        self.max_results.setValue(s.value("max", 10000, type=int))
        alpha = s.value("alphabet", "", type=str) or ""
        self._restored_alpha = bool(alpha)
        self.alphabet_edit.setPlainText(alpha)
        self._apply_style()

    def closeEvent(self, e):
        s = self.S
        s.setValue("geometry", self.saveGeometry())
        s.setValue("windowState", self.saveState())
        s.setValue("dark", self.dark)
        s.setValue("fontpt", self.font_pt)
        s.setValue("lang", self.lang_combo.currentData() or "python")
        s.setValue("mode", self.mode.currentIndex())
        s.setValue("n", self.n_spin.value())
        s.setValue("sep", self.sep.currentIndex())
        s.setValue("pyflakes", self.chk_py.isChecked())
        s.setValue("strict", self.chk_strict.isChecked())
        s.setValue("agg", self.chk_agg.isChecked())
        s.setValue("max", self.max_results.value())
        s.setValue("alphabet", self.alphabet_edit.toPlainText())
        s.setValue("lastdir", self._last_dir)
        if self.worker is not None and self.worker.isRunning():
            self.worker.cancel(); self.worker.wait(3000)
            if self.worker.isRunning(): self.worker.terminate()
        e.accept()

    # ------------------------------------------------------------- handlers --
    def _cur_lang(self): return LANG_BY_KEY[self.lang_combo.currentData()]

    def _on_lang(self, _idx=0):
        lang = self._cur_lang()
        dep_txt = status = ""
        if lang.missing:
            pips = " ".join(p for _, p in lang.missing)
            dep_txt = f" — <span style='color:#b00;'>missing: pip install {pips}</span>"
        elif lang.live is not None and not lang.live():
            status = (" <span style='color:#b50;'>— engine inactive: "
                      "structural fallback in use</span>")
        opts = " ".join(p for _, p in lang.optional)
        opt_txt = f" &nbsp;(optional: {opts})" if opts else ""
        self.engine_lbl.setText(
            f"{lang.emoji} <b>{lang.name}</b> · engine: {lang.engine}"
            f"{status}{dep_txt}{opt_txt}<br><small>pruner: {lang.note}</small>")
        is_py = lang.pyflakes
        self.chk_py.setVisible(is_py); self.chk_strict.setVisible(is_py)
        self._refresh_highlighter(lang.key)
        self._apply_style()
        self._on_mode()
        self._update_results_title()

    def _on_mode(self, _idx=0):
        lang, toks = self._cur_lang(), self.mode.currentIndex() == 1
        self.sep.setEnabled(toks); self.chk_agg.setEnabled(toks)
        self.preset.blockSignals(True); self.preset.clear()
        for label, _t in lang.presets.get("tokens" if toks else "chars", []):
            self.preset.addItem(label)
        self.preset.blockSignals(False)
        if self.preset.count():
            self._apply_preset(0)
        self._update_alpha_info()

    def _on_preset(self, idx):
        self._apply_preset(idx)

    def _apply_preset(self, idx):
        if idx < 0 or self._restoring:
            return
        toks = self.mode.currentIndex() == 1
        presets = self._cur_lang().presets.get("tokens" if toks else "chars", [])
        if idx < len(presets):
            self.alphabet_edit.setPlainText(presets[idx][1])

    def _update_alpha_info(self):
        text = self.alphabet_edit.toPlainText()
        if self.mode.currentIndex() == 0:
            k = len(set(text.replace("\r", "").replace("\n", "")))
        else:
            k = len(dict.fromkeys(t for t in re.split(r"[\s,]+", text) if t))
        self.alpha_k = k
        self._update_space()

    def _update_space(self, *_):
        k = getattr(self, "alpha_k", 0)
        n = self.n_spin.value()
        est = k ** n if k else 0
        if est > 10 ** 7:
            self.space_lbl.setText(f"search space: {_human(est)} ⚠")
            self.space_lbl.setStyleSheet("color:#c33; font-weight:bold;")
        else:
            self.space_lbl.setText(f"search space: {_human(est)}")
            self.space_lbl.setStyleSheet("")

    # ------------------------------------------------------------- running --
    def _start(self):
        if self.worker is not None:
            return
        lang = self._cur_lang()
        if lang.missing:
            pips = ", ".join(p for _, p in lang.missing)
            QMessageBox.information(self, "Dependency missing",
                                    f"{lang.name} validation requires: {pips}\n\n"
                                    f"pip install {pips}")
            return
        is_tokens = self.mode.currentIndex() == 1
        n = self.n_spin.value()
        text = self.alphabet_edit.toPlainText()
        if is_tokens:
            seen, tokens = set(), []
            for t in re.split(r"[\s,]+", text):
                if t and t not in seen:
                    seen.add(t); tokens.append(t)
            alphabet, k = "", len(tokens)
        else:
            tokens = []
            alphabet = "".join(sorted(set(text.replace("\r", "").replace("\n", ""))))
            k = len(alphabet)
        if k == 0:
            QMessageBox.information(self, "Empty alphabet",
                                    "Provide at least one character/token.")
            return
        est = k ** n
        if est > 10_000_000:
            warn = (f"{k} ** {n} = {_human(est)} candidates.\n"
                    + ("This language has NO prefix pruner — every candidate is "
                       "validated. Keep n small!" if lang.make_machine() is None else
                       "Memory is fine (iterative DFS) but this can take a very long time.")
                    + "\n\nStart anyway?")
            if QMessageBox.question(self, "Huge search space", warn,
                                    QMessageBox.StandardButton.Yes |
                                    QMessageBox.StandardButton.No) \
               != QMessageBox.StandardButton.Yes:
                return
        cfg = dict(mode="tokens" if is_tokens else "chars", lang=lang.key,
                   alphabet=alphabet, tokens=tokens, n=n,
                   sep="" if self.sep.currentIndex() == 0 else " ",
                   use_pyflakes=HAS_PYFLAKES and self.chk_py.isChecked(),
                   strict=self.chk_strict.isChecked(),
                   aggressive=self.chk_agg.isChecked(),
                   max_results=self.max_results.value())
        self.results.clear(); self.preview.clear()
        self._found_total = self._visible = 0
        self._capped = False
        self._update_results_title()
        self.graph.clear(); self.progress.setValue(0)
        self.workbar.set_values(0, 0, 0)
        for lbl in self.tiles.values():
            lbl.setText("—")
        self.sm.set_message("select a result to see its lexical structure")
        self.heat.set_items([])
        self.filter_edit.blockSignals(True)
        self.filter_edit.clear()
        self.filter_edit.blockSignals(False)
        self.results.hint = "Enumerating…"
        self.results.viewport().update()
        self._t0 = time.perf_counter()
        self.worker = Enumerator(cfg)
        self.worker.found_batch.connect(self._on_found)
        self.worker.stats.connect(self._on_stats)
        self.worker.progress.connect(self.progress.setValue)
        self.worker.finished_run.connect(self._on_done)
        self._set_running(True)
        self.worker.start()
        self.statusBar().showMessage(
            f"Enumerating {lang.name} programs… (parsed, never executed)")

    def _stop(self):
        if self.worker is not None:
            self.worker.cancel()
            self.statusBar().showMessage("Stopping…")

    def _toggle_pause(self):
        w = self.worker
        if w is None:
            return
        if w._paused:
            w.resume()
            self.pause_btn.setText("⏸ Pause"); self.a_pause.setText("Pause")
            self.statusBar().showMessage("Resumed.")
        else:
            w.pause()
            self.pause_btn.setText("▶ Resume"); self.a_pause.setText("Resume")
            self.statusBar().showMessage("Paused — press again to resume.")

    def _set_running(self, running):
        for w in (self.lang_combo, self.preset, self.n_spin, self.mode, self.sep,
                  self.alphabet_edit, self.chk_py, self.chk_strict, self.chk_agg,
                  self.max_results, self.start_btn, self.scratch_btn):
            w.setEnabled(not running)
        self.stop_btn.setEnabled(running)
        self.pause_btn.setEnabled(running)
        self.a_pause.setEnabled(running)
        self.spin_lbl.setVisible(running)
        if running:
            self.spin_timer.start()
        else:
            self.spin_timer.stop()
            self.pause_btn.setText("⏸ Pause")
            self.a_pause.setText("Pause")

    # ------------------------------------------------------------- results --
    def _on_found(self, batch):
        f = self.filter_edit.text().strip().lower()
        star_only = self.chk_star.isChecked()
        for src in batch:
            self._found_total += 1
            if self.results.count() >= 100_000:
                self._capped = True
                continue
            it = QListWidgetItem()
            it.setData(Qt.ItemDataRole.UserRole, src)
            it.setData(Qt.ItemDataRole.UserRole + 1, False)
            it.setData(Qt.ItemDataRole.UserRole + 2, self.lang_combo.currentData())
            it.setText(ResultsList._disp(src))
            it.setToolTip(src[:2000])
            ok = (not f or f in src.lower()) and not star_only
            it.setHidden(not ok)
            self._visible += ok
            self.results.addItem(it)
        self._update_results_title()
        self._schedule_overview()

    def _apply_filter(self):
        f = self.filter_edit.text().strip().lower()
        star_only = self.chk_star.isChecked()
        vis = 0
        for i in range(self.results.count()):
            it = self.results.item(i)
            src = it.data(Qt.ItemDataRole.UserRole)
            ok = (not f or f in src.lower()) and \
                 (not star_only or it.data(Qt.ItemDataRole.UserRole + 1))
            it.setHidden(not ok)
            vis += ok
        self._visible = vis
        self._update_results_title()
        self._schedule_overview()

    def _update_results_title(self):
        lang = self._cur_lang() if self.lang_combo.count() else None
        head = f"{lang.emoji} {lang.name} — " if lang else ""
        t = f"{head}Valid programs: {self._found_total:,}"
        flt = bool(self.filter_edit.text().strip()) or self.chk_star.isChecked()
        if flt:
            t += f" &nbsp;·&nbsp; showing {self._visible:,}"
        if self._capped:
            t += (" &nbsp;<span style='color:#b50;'>· display capped at 100,000 "
                  "(counts continue)</span>")
        self.results_title.setText(t)

    def _on_stats(self, d):
        el = time.perf_counter() - self._t0 if self._t0 else d["elapsed"]
        rate = d["checked"] / el if el > 0.05 else 0.0
        self.graph.add(el, rate)
        self.workbar.set_values(d["est"], d["checked"], d["elim"])
        rem = max((d["est"] or 0) - d["checked"] - d["elim"], 0)
        eta = rem / rate if rate > 0 else None
        eta_s = _eta(eta)
        self.progress.setFormat(f"%p% · ETA {eta_s}")
        self.tiles["valid"].setText(f"{d['valid']:,}")
        self.tiles["checked"].setText(f"{d['checked']:,}")
        self.tiles["pruned"].setText(f"{d['pruned']:,}")
        self.tiles["elim"].setText(_human(d["elim"]))
        self.tiles["rate"].setText(f"{rate:,.0f}/s")
        self.tiles["eta"].setText(eta_s)
        if self.worker is not None:
            self.setWindowTitle(
                f"{self._base_title} — {self.progress.value() / 10:.0f}% · ETA {eta_s}")

    def _on_done(self, msg):
        if self.worker is not None:
            self.worker.wait(); self.worker = None
        self._set_running(False)
        self.setWindowTitle(self._base_title)
        self.results.hint = ("No results yet.\n"
                             "Press Ctrl+⏎ to start — candidates are parsed, never executed.")
        self.results.viewport().update()
        self.statusBar().showMessage(msg, 20000)
        self.toast.show_msg(msg)
        QApplication.beep()

    def _set_chip(self, lbl, text, colors=None):
        lbl.setText(text)
        if colors is None:
            lbl.setStyleSheet("color: palette(mid);")
        else:
            bg, fg = colors
            lbl.setStyleSheet(
                f"QLabel#pill {{ background: {bg}; color: {fg}; "
                f"border-radius: 10px; padding: 2px 10px; font-weight: 600; }}")

    def _star_current(self):
        it = self.results.currentItem()
        if it is not None:
            self.results.toggle_star(it)
            self.toast.show_msg("★ starred" if it.data(Qt.ItemDataRole.UserRole + 1)
                                else "☆ unstarred")

    # ------------------------------------------------- copy / export / misc --
    def _copy_selected(self):
        items = self.results.selectedItems()
        if items:
            QApplication.clipboard().setText(
                "\n".join(i.data(Qt.ItemDataRole.UserRole) for i in items))
            self.toast.show_msg(f"Copied {len(items)} result(s)")

    def _copy_all(self):
        srcs = self._collect(starred_only=False)
        if not srcs:
            self.statusBar().showMessage("Nothing to copy.", 5000); return
        QApplication.clipboard().setText("\n".join(srcs))
        self.toast.show_msg(f"Copied {len(srcs)} result(s)")

    def _clear_results(self):
        if self.worker is not None:
            return
        self.results.clear(); self.preview.clear()
        self._found_total = self._visible = 0
        self._capped = False
        self._update_results_title()
        self.heat.set_items([])
        self.sm.set_message("select a result to see its lexical structure")
        self._set_chip(self.chip_status, "—", None)
        self._set_chip(self.chip_engine, "", None)

    def _collect(self, starred_only):
        out = []
        for i in range(self.results.count()):
            it = self.results.item(i)
            if starred_only:
                if it.data(Qt.ItemDataRole.UserRole + 1):
                    out.append(it.data(Qt.ItemDataRole.UserRole))
            elif not it.isHidden():
                out.append(it.data(Qt.ItemDataRole.UserRole))
        return out

    def _export(self, starred_only=False):
        srcs = self._collect(starred_only)
        if not srcs:
            self.statusBar().showMessage("Nothing to export.", 5000); return
        lang = self._cur_lang()
        suffix = "_starred" if starred_only else ""
        default = f"{lang.key}_n{self.n_spin.value()}{suffix}.json"
        path, _flt = QFileDialog.getSaveFileName(
            self, "Export results", os.path.join(self._last_dir, default),
            "JSON (*.json);;Text blocks (*.txt);;CSV (*.csv)")
        if not path:
            return
        self._last_dir = os.path.dirname(path)
        self.S.setValue("lastdir", self._last_dir)
        try:
            if path.lower().endswith(".csv"):
                with open(path, "w", newline="", encoding="utf-8") as fh:
                    w = csv.writer(fh)
                    w.writerow(["index", "length", "source"])
                    for i, s in enumerate(srcs, 1):
                        w.writerow([i, len(s), s])
            elif path.lower().endswith(".txt"):
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(f"# language={lang.key}  n={self.n_spin.value()}  "
                             f"count={len(srcs)}\n")
                    for i, s in enumerate(srcs, 1):
                        fh.write(f"\n{'────' * 3} {i} {'────' * 3}\n{s}\n")
            else:
                if not path.lower().endswith(".json"):
                    path += ".json"
                with open(path, "w", encoding="utf-8") as fh:
                    json.dump({"language": lang.key, "n": self.n_spin.value(),
                               "count": len(srcs), "results": srcs}, fh,
                              ensure_ascii=False, indent=1)
        except Exception as e:
            QMessageBox.critical(self, "Export failed", f"{e!r}")
            return
        self.toast.show_msg(f"Exported {len(srcs)} result(s)")

    def _results_menu(self, pos):
        it = self.results.itemAt(pos)
        menu = QMenu(self)
        if it is not None:
            star = it.data(Qt.ItemDataRole.UserRole + 1)
            menu.addAction(("☆ Unstar" if star else "★ Star") + "   (S)",
                           lambda: self.results.toggle_star(it))
            menu.addAction("Copy", self._copy_selected)
            menu.addAction("Show validation in preview", self._show_preview)
            menu.addSeparator()
        menu.addAction("Copy all (filtered)", self._copy_all)
        menu.addAction("Export visible results…", lambda: self._export(False))
        menu.addAction("Export ★ starred…", lambda: self._export(True))
        menu.exec(self.results.viewport().mapToGlobal(pos))

    # ------------------------------------------------------- preview pane --
    def _show_preview(self):
        items = self.results.selectedItems()
        if not items:
            self.preview.clear()
            self._set_chip(self.chip_status, "—", None)
            self._set_chip(self.chip_engine, "", None)
            self.sm.set_message("select a result to see its lexical structure")
            self.chip_copy.setEnabled(False); self.chip_star.setEnabled(False)
            return
        self.chip_copy.setEnabled(True); self.chip_star.setEnabled(True)
        src = items[0].data(Qt.ItemDataRole.UserRole)
        key = items[0].data(Qt.ItemDataRole.UserRole + 2) \
            or self.lang_combo.currentData()
        if self._hl_lang != key:
            self._refresh_highlighter(key)
        lang = LANG_BY_KEY[key]
        self._set_chip(self.chip_engine, f"{lang.emoji} {lang.engine}")
        if self.worker is not None:
            self.preview.setPlainText(
                src + "\n\n" + "─" * 46 +
                "\nvalidation deferred until the current run finishes "
                "(keeps parser use single-threaded).")
            self._set_chip(self.chip_status, "DEFERRED",
                           ("#b8860b", "#10141a" if self.dark else "#fff"))
            self.sm.set_message("validation deferred until the run finishes")
            return
        ok, msgs = lang.validate(src)
        if ok and lang.pyflakes and self.chk_py.isChecked() and HAS_PYFLAKES:
            out = pyflakes_report(src)
            if out and out.strip():
                msgs = msgs + [out.strip()]
        good = "#2e7d32" if self.dark else "#1b7e3c"
        badp = "#c0392b"
        bgc = ("rgba(46,125,50,0.22)" if ok else "rgba(192,57,43,0.22)")
        self._set_chip(self.chip_status, "✓ VALID" if ok else "✗ INVALID",
                       (bgc, "#eaf7ec" if ok else "#fdecea"))
        lines = [src, "", "─" * 46,
                 f"{lang.engine} : " + ("✓ valid" if ok else "✗ invalid")]
        lines += ["• " + m for m in msgs]
        lines += ["", "Static validation only — this candidate was never executed."]
        self.preview.setPlainText("\n".join(lines))
        m = lang.make_machine()
        if isinstance(m, GenericLexMachine):
            regions, prof, sok, why = _scan_visual_generic(m.spec, src)
            self.sm.set_result(regions, prof, sok, why)
        else:
            self.sm.set_message("no lexical model for this language "
                                "(structure map unavailable)")

    def _validate_scratch(self):
        lang = self._cur_lang()
        src = self.scratch.toPlainText()
        if not src.strip():
            self.scratch_out.setPlainText("(nothing to validate)"); return
        ok, msgs = lang.validate(src)
        if ok and lang.pyflakes and HAS_PYFLAKES and self.chk_py.isChecked():
            out = pyflakes_report(src)
            if out and out.strip():
                msgs = msgs + [out.strip()]
        head = f"{lang.emoji} {lang.name}: " + ("✓ VALID — static check only" if ok
                                                else "✗ INVALID")
        self.scratch_out.setPlainText("\n".join([head] + ["• " + m for m in msgs]))

    def _engine_report(self):
        rows = []
        for l in LANGS:
            if l.missing:
                st = "✗ missing deps: pip install " + " ".join(p for _, p in l.missing)
            elif l.live is not None:
                st = "✓ active" if l.live() else "△ inactive — structural fallback"
            else:
                st = "✓ active"
            rows.append(f"{l.emoji} {l.name:<24} {st}")
        QMessageBox.information(
            self, "Engine status",
            "Static validation engines (nothing is ever executed):\n\n"
            + "\n".join(rows))

    def _shortcuts_dlg(self):
        QMessageBox.information(self, "Keyboard shortcuts", SHORTCUTS_TEXT)

    def _about(self):
        QMessageBox.about(
            self, "About",
            "<b>Program Enumerator</b><br><br>"
            "Generates all programs of length n over a character alphabet or "
            "token set and keeps the statically valid ones.<br><br>"
            "Candidates are <b>never executed</b> — only parsers/linters touch "
            "them (ast.parse, tree-sitter, fparser2, …). Sound lexical NFAs "
            "prune impossible prefixes; <code>--selftest</code> verifies every "
            "pruner against brute force.<br><br>"
            "Visuals: per-language accent themes, stat tiles, work-saved bar, "
            "structure map, heat-grid overview, toasts.")


# =========================================================================== #
# 9) Self-test & CLI
# =========================================================================== #
def _selftest():
    if QCoreApplication.instance() is None:
        _app = QCoreApplication(sys.argv)  # noqa: F841
    cases = [("python", "()+1", 4), ("python", "1+'\"", 4), ("python", "1+#\\\n", 4),
             ("json", '{}[]",:1', 4), ("lisp", "()'\"a;", 4), ("brainfuck", "[]+.", 4),
             ("regex", "()[]a1\\^", 3), ("html", "<>a/", 4), ("xml", "<>a/", 4),
             ("generic", "{}()[];1", 3),
             ("go", 'fn(){};="1a', 3), ("csharp", '(){};="1a@', 3),
             ("cpp", '(){};="R1a<', 3), ("rust", 'fn(){};"r#1a', 3),
             ("haskell", "(){}\"a1='-{-", 3), ("pascal", "()';{}*1a", 3),
             ("fortran", "()'\"!*1a", 3)]
    if LANG_BY_KEY["javascript"].available:
        cases.append(("javascript", ";1+a", 3))
    fails = 0
    for key, alpha, n in cases:
        lang = LANG_BY_KEY[key]
        live = "structural" if (lang.live is not None and not lang.live()) \
            else "real engine"
        brute = {s for tup in itertools.product(alpha, repeat=n)
                 for s in ("".join(tup),) if lang.validate(s)[0]}
        cfg = dict(mode="chars", lang=key, alphabet=alpha, tokens=[], n=n, sep="",
                   use_pyflakes=False, strict=False, aggressive=True,
                   max_results=10 ** 9)
        w = Enumerator(cfg); got = []
        w.found_batch.connect(got.extend); w.run()
        if set(got) != brute:
            fails += 1
            print(f"FAIL {key} {alpha!r} n={n} [{live}]")
            print("  missing:", sorted(brute - set(got))[:10])
            print("  extra  :", sorted(set(got) - brute)[:10])
        else:
            print(f"ok  {key:<10} {alpha!r} n={n}: {len(brute)} valid — "
                  f"matches brute force [{live}]")
    if fails:
        print(f"selftest FAILED ({fails})"); return 1
    print("selftest passed ✓  (all pruners are sound)")
    return 0

def _list_langs():
    print(f"{'key':<12} {'language':<28} {'engine':<46} {'deps'}")
    for l in LANGS:
        req = ", ".join(p for _, p in l.missing) if l.missing else ""
        opt = " (opt: " + ", ".join(p for _, p in l.optional) + ")" if l.optional else ""
        print(f"{l.key:<12} {l.name:<28} {l.engine:<46} {req}{opt}")
    return 0

def _cli(a):
    lang = LANG_BY_KEY.get(a.lang)
    if lang is None:
        print(f"unknown language {a.lang!r} — use --list"); return 2
    if lang.missing:
        print(f"{lang.name} needs: " + ", ".join(p for _, p in lang.missing)); return 2
    toks = [t for t in re.split(r"[\s,]+", a.alpha) if t] if a.tokens else []
    cfg = dict(mode="tokens" if a.tokens else "chars", lang=a.lang,
               alphabet="" if a.tokens else a.alpha, tokens=toks, n=a.length,
               sep=a.sep, use_pyflakes=a.pyflakes and lang.pyflakes,
               strict=a.strict, aggressive=not a.no_prune, max_results=a.max)
    w = Enumerator(cfg); found = []
    w.found_batch.connect(found.extend); w.stats.connect(lambda d: None)
    t0 = time.perf_counter(); w.run()
    for s in found:
        print(repr(s))
    if a.out:
        with open(a.out, "w", encoding="utf-8") as fh:
            json.dump({"language": a.lang, "n": a.length, "count": len(found),
                       "results": found}, fh, ensure_ascii=False, indent=1)
        print(f"wrote {a.out}")
    print(f"-- {len(found)} valid / {w._checked} validated / "
          f"{w._pruned} nodes pruned in {time.perf_counter() - t0:.2f}s")
    return 0

def main():
    ap = argparse.ArgumentParser(
        description="Enumerate & statically validate all programs of length n "
                    "(many languages)")
    ap.add_argument("--selftest", action="store_true",
                    help="verify pruners vs brute force, then exit")
    ap.add_argument("--list", action="store_true",
                    help="list languages and dependencies")
    ap.add_argument("--cli", action="store_true", help="headless run (no GUI)")
    ap.add_argument("--lang", default="python", help="language key (see --list)")
    ap.add_argument("--alpha", default=None, help="alphabet or token list")
    ap.add_argument("-n", "--length", type=int, default=4)
    ap.add_argument("--tokens", action="store_true",
                    help="treat --alpha as tokens")
    ap.add_argument("--sep", default="", help="joiner between tokens (token mode)")
    ap.add_argument("--max", type=int, default=1000)
    ap.add_argument("--out", default=None, help="write results to a JSON file (cli)")
    ap.add_argument("--pyflakes", action="store_true")
    ap.add_argument("--strict", action="store_true")
    ap.add_argument("--no-prune", action="store_true")
    args = ap.parse_args()

    if args.selftest: sys.exit(_selftest())
    if args.list:     sys.exit(_list_langs())
    if args.alpha is None:
        lang = LANG_BY_KEY[args.lang]
        args.alpha = (lang.presets["tokens"] if args.tokens
                      else lang.presets["chars"])[0][1]
    if args.cli:
        sys.exit(_cli(args))

    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    win = MainWindow(); win.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
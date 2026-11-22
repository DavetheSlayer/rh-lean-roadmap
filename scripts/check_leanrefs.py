#!/usr/bin/env python3
"""Check the book's Lean citations against a Lean source tree.

Two citation formats carry a module and are checked (both with the same rules below):
  * `\\leanref{decl}{module}{a--b}` (appendix proofs);
  * index entries `\\texttt{decl} (\\texttt{module}, lines a--b)` (the range must be `n`, `a--b` or a comma-separated list of these,
    else the entry is malformed and the run fails) (the "Index of Lean
    declarations"; `\\_` and `\\allowbreak{}` are stripped from names).
NOT checked: the main-text `\\leanrefs{\\texttt{...}}` lists, which name declarations without
a module; they are not cross-checked against the index.

This is a lexical check, NOT elaborated name resolution (it does not run Lean, resolve
`open`/`export`, or follow imports). For every \\leanref in the given .tex files it checks:
  1. the module maps to an existing file <root>/<Module/Path>.lean;
  2. the declaration is introduced in that file. Lean comments (`--` and nested `/- -/`,
     including doc comments) and string literals are ignored. A declaration is a
     theorem/lemma/def/structure/abbrev/instance/class/inductive/opaque/axiom/irreducible_def
     command (optionally after attributes/modifiers) or a field of a `structure`/`class`
     body (only lines at the body's field indentation, from the `where` line until the next
     top-level command).
  3. Name rule. The declared name token is read completely, so `A.leaf.child` never counts
     as `leaf`: the token must end exactly at the cited leaf. A QUALIFIED citation (contains
     a dot) must equal the declaration's reconstructed full name: the enclosing `namespace`
     blocks followed by the written token (a declaration written `_root_.X` declares `X`; a
     citation `_root_.X` means exactly the root-level `X`, even when `X` has no dot). No suffix or relative matching is done. An unqualified
     citation (no dot) matches on the leaf alone.
  4. (--lines, advisory) a sanity check of the cited range only: parseable, inside the
     file, and the declaration does not start after the range ends. It does NOT check that
     the declaration lies inside the range (the book's ranges often cover just the proof).

Exit status: 1 if any citation fails or if no \\leanref was found at all, else 0.

Usage:
  python3 scripts/check_leanrefs.py LEAN_SRC_ROOT [--tex FILE ...] [--skip-mathlib] [--lines]
"""
import argparse, re, sys
from collections import namedtuple
from pathlib import Path

DEFAULT_TEX = ["docs/src/book/main.tex"]


def clean(s):
    s = s.replace("\\allowbreak", "").replace("{}", "")
    s = s.replace("\\_", "_").replace("--", "-")
    return re.sub(r"\s+", "", s)


def read_group(text, i):
    """text[i] == '{'; return (content, index after matching '}')."""
    assert text[i] == "{"
    depth, j = 0, i
    while j < len(text):
        c = text[j]
        if c == "\\":
            j += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return text[i + 1:j], j + 1
        j += 1
    raise ValueError("unbalanced braces")


def parse_leanrefs(path):
    text = path.read_text(encoding="utf-8", errors="replace")
    # drop comments (unescaped %) so commented-out macros are ignored
    text_nc = re.sub(r"(?<!\\)%[^\n]*", lambda m: " " * len(m.group(0)), text)
    out = []
    for m in re.finditer(r"\\leanref(?![A-Za-z])", text_nc):
        i = m.end()
        args = []
        try:
            for _ in range(3):
                while text_nc[i] in " \t\r\n":
                    i += 1
                g, i = read_group(text_nc, i)
                args.append(g)
        except (IndexError, ValueError, AssertionError):
            out.append((text.count("\n", 0, m.start()) + 1, None))
            continue
        out.append((text.count("\n", 0, m.start()) + 1, tuple(clean(a) for a in args)))
    return out


INDEX_RE = re.compile(r"\\texttt\{((?:[^{}]|\{\})*)\}\s*\(\\texttt\{((?:[^{}]|\{\})*)\},\s*lines\s+([^()]*)\)")
MalformedRange = namedtuple("MalformedRange", "decl range")  # index entry whose range is not `n` or `a--b`
_RNG = r"\d+(?:--\d+)?"
INDEX_RANGE_RE = re.compile(_RNG + "(?:," + _RNG + ")*")  # `n`, `a--b`, or a comma-separated list of these; nothing else is well-formed
LINES_RE = re.compile(r",\s*lines\s")


def parse_index(path):
    """Index entries `\\texttt{decl} (\\texttt{module}, lines a--b)`; same tuple shape as parse_leanrefs.
    A `, lines ` that is not part of a well-formed entry, or an entry whose range is not `n` or
    `a--b`, is malformed: returned as None / MalformedRange(decl, range)."""
    text = path.read_text(encoding="utf-8", errors="replace")
    text_nc = re.sub(r"(?<!\\)%[^\n]*", lambda m: " " * len(m.group(0)), text)
    out, spans = [], []
    for m in INDEX_RE.finditer(text_nc):
        spans.append((m.start(), m.end()))
        ln = text.count("\n", 0, m.start()) + 1
        if not INDEX_RANGE_RE.fullmatch(m.group(3).strip()):
            out.append((ln, MalformedRange(clean(m.group(1)), clean(m.group(3)))))
            continue
        out.append((ln, tuple(clean(m.group(k)) for k in (1, 2, 3))))
    for m in LINES_RE.finditer(text_nc):
        if not any(a <= m.start() < b for a, b in spans):
            out.append((text.count("\n", 0, m.start()) + 1, None))
    return out


def strip_lean_comments(src):
    """Blank out `--` comments, nested `/- -/` comments and string literals, keeping newlines."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        two = src[i:i + 2]
        if depth:
            if two == "/-":
                depth += 1; out.append("  "); i += 2
            elif two == "-/":
                depth -= 1; out.append("  "); i += 2
            else:
                out.append("\n" if src[i] == "\n" else " "); i += 1
        elif two == "/-":
            depth = 1; out.append("  "); i += 2
        elif two == "--":
            while i < n and src[i] != "\n":
                out.append(" "); i += 1
        elif src[i] == '"':
            out.append(" "); i += 1
            while i < n and src[i] != '"':
                if src[i] == "\\" and i + 1 < n:
                    out.append(" "); i += 1
                out.append("\n" if src[i] == "\n" else " "); i += 1
            out.append(" "); i += 1
        else:
            out.append(src[i]); i += 1
    return "".join(out)


MODS = r"(?:(?:@\[[^\]]*\]|private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
DECL_RE = re.compile(r"^\s*" + MODS + r"(?:class\s+inductive|theorem|lemma|def|structure|abbrev|instance|class|inductive|opaque|axiom|irreducible_def)\s+([^\s:({\[⦃⟨]+)")
STRUCT_RE = re.compile(r"^\s*" + MODS + r"(?:structure|class)\s+([^\s:({\[⦃⟨]+)")
NS_RE = re.compile(r"^\s*namespace\s+(\S+)")
SEC_RE = re.compile(r"^\s*(?:noncomputable\s+)?section\b")
END_RE = re.compile(r"^\s*end\b(?:\s+(\S+))?")
FIELD_RE = re.compile(r"^(\s+)((?:[\w'.«»!?]+\s+)*[\w'.«»!?]+)\s*:(?!=)")
# any top-level command at column 0 ends a structure body
TOP_RE = re.compile(r"^\S")


def declarations(file):
    """Return ([(written_name, full_name, line)], number_of_lines) for a Lean file."""
    lines = strip_lean_comments(file.read_text(encoding="utf-8", errors="replace")).split("\n")
    stack = []        # entries: list of namespace components ([] for `section`)
    decls = []        # (written, full, line)
    struct = None     # dict(full=..., pending=bool, indent=None)
    def ns():
        return [c for e in stack for c in e]
    def full_of(tok):
        if tok.startswith("_root_."):
            return tok[len("_root_."):]
        return ".".join(ns() + [tok]) if ns() else tok
    for n, l in enumerate(lines, 1):
        sm = STRUCT_RE.match(l)
        # a new column-0 command ends any open structure body / pending header
        if struct is not None and TOP_RE.match(l) and not (struct["header_line"] == n):
            struct = None
        m = NS_RE.match(l)
        if m:
            stack.append(m.group(1).split("."))
            continue
        if SEC_RE.match(l):
            stack.append([]); continue
        m = END_RE.match(l)
        if m and TOP_RE.match(l):
            if stack:
                stack.pop()
            continue
        if sm:
            tok = sm.group(1)
            decls.append((tok.replace("_root_.", "", 1) if tok.startswith("_root_.") else tok, full_of(tok), n))
            struct = {"full": full_of(tok), "pending": True, "indent": None, "header_line": n}
        else:
            m = DECL_RE.match(l)
            if m:
                tok = m.group(1)
                decls.append((tok[len("_root_."):] if tok.startswith("_root_.") else tok, full_of(tok), n))
        if struct is not None:
            if struct["pending"]:
                if re.search(r"\bwhere\b", l):
                    struct["pending"] = False
                continue
            if struct["header_line"] == n:
                continue
            fm = FIELD_RE.match(l)
            if fm:
                ind = len(fm.group(1))
                if struct["indent"] is None:
                    struct["indent"] = ind
                if ind == struct["indent"]:
                    for nm in fm.group(2).split():
                        decls.append((nm, struct["full"] + "." + nm, n))
            elif l.strip() and struct["indent"] is None:
                struct["indent"] = len(l) - len(l.lstrip())
    return decls, len(lines)


def name_matches(cited, written, full):
    absolute = cited.startswith("_root_.")
    if absolute:
        cited = cited[len("_root_."):]
    parts = cited.split(".")
    if full.split(".")[-1] != parts[-1]:
        return False
    if len(parts) == 1 and not absolute:
        return True
    return cited == full


_cache = {}


def lookup(file, cited):
    """Return (line numbers where `cited` is declared in `file`, total line count)."""
    if file not in _cache:
        _cache[file] = declarations(file)
    decls, nlines = _cache[file]
    return [ln for (w, f, ln) in decls if name_matches(cited, w, f)], nlines


MATHLIB = ("Mathlib", "Batteries", "Std", "Lean", "Init", "Aesop", "Qq")


def check(root, tex_files, skip_mathlib=False, lines=False, stats=None):
    """Return (checked, skipped, errors). `checked` excludes skipped. If `stats` is a dict it is
    filled with {format: [checked, skipped, malformed]} for the formats "leanref" and "index".
    Malformed entries are reported as errors and counted separately (not in `checked`)."""
    st = stats if stats is not None else {}
    st.update({"leanref": [0, 0, 0], "index": [0, 0, 0]})
    errors = []
    for tex in tex_files:
        for fmt, parse, what in (("leanref", parse_leanrefs, "\\leanref"),
                                 ("index", parse_index, "index entry")):
            for line, args in parse(Path(tex)):
                where = f"{tex}:{line}"
                if args is None:
                    errors.append(f"{where}: malformed {what} (could not read declaration, module and lines)")
                    st[fmt][2] += 1
                    continue
                if isinstance(args, MalformedRange):
                    errors.append(f"{where}: malformed {what}: range `{args.range}` is not `n`, `a--b` or a list of these (declaration {args.decl})")
                    st[fmt][2] += 1
                    continue
                decl, mod, rng = args
                if skip_mathlib and mod.split(".")[0] in MATHLIB:
                    st[fmt][1] += 1
                    continue
                st[fmt][0] += 1
                f = Path(root) / (mod.replace(".", "/") + ".lean")
                if not f.is_file():
                    errors.append(f"{where}: module not found: {mod}  (declaration {decl}) [{fmt}]")
                    continue
                hits, nlines = lookup(f, decl)
                if not hits:
                    errors.append(f"{where}: `{decl}` is not declared in {mod} [{fmt}]")
                    continue
                if lines:
                    if not re.fullmatch(r"\d+(-\d+)?(,\d+(-\d+)?)*", rng):
                        errors.append(f"{where}: cannot parse line range `{rng}`")
                        continue
                    hi = max(int(x) for x in re.findall(r"\d+", rng))
                    if hi > nlines + 1:  # tolerate a trailing-newline "line"
                        errors.append(f"{where}: cited lines {rng} exceed the {nlines} lines of {mod}")
                    elif min(hits) > hi:
                        errors.append(f"{where}: `{decl}` in {mod} is declared at line(s) {hits}, after cited {rng}")
    checked = sum(v[0] for v in st.values())
    skipped = sum(v[1] for v in st.values())
    if checked + skipped + sum(v[2] for v in st.values()) == 0:
        errors.append("no \\leanref or index entry found in " + ", ".join(map(str, tex_files)))
    elif checked == 0 and skipped:
        errors.append(f"all {skipped} citations were skipped, nothing was checked")
    return checked, skipped, errors


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("root", type=Path, help="Lean source root, e.g. TomasOrtega/RH extracted/lean/src")
    ap.add_argument("--tex", nargs="+", type=Path, default=[Path(p) for p in DEFAULT_TEX])
    ap.add_argument("--skip-mathlib", action="store_true", help="skip modules starting with Mathlib/Batteries/Std/Lean/Init")
    ap.add_argument("--lines", action="store_true",
                    help="advisory range sanity check: range parses, lies inside the file, and the declaration "
                         "does not start after it ends (does not verify the declaration is inside the range)")
    a = ap.parse_args(argv)
    st = {}
    total, skipped, errors = check(a.root, a.tex, a.skip_mathlib, a.lines, st)
    for e in errors:
        print("FAIL", e)
    for k, name in (("leanref", "\\leanref"), ("index", "index entries")):
        print(f"{name}: {st[k][0]:,} checked plus {st[k][1]:,} skipped, {st[k][2]} malformed")
    print("not checked: main-text \\leanrefs{\\texttt{...}} lists (no module given)")
    mal = sum(v[2] for v in st.values())
    print(f"total: {total:,} checked plus {skipped:,} skipped, {mal} malformed, {len(errors)} failed (malformed included)")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Check the book's \\leanref{decl}{module}{lines} citations against a Lean source tree.

For every \\leanref in the given .tex files this checks that
  1. the module maps to an existing file <root>/<Module/Path>.lean,
  2. the last component of the declaration name is declared in that file
     (theorem, lemma, def, structure, abbrev, instance, class, inductive, ...,
     or a structure field),
  3. (with --lines) the cited line range is plausible: it lies inside the file and the
     declaration starts at or before the end of the range. The book's ranges often cover
     only the proof body, so a declaration starting before the range is accepted.

Usage:
  python3 scripts/check_leanrefs.py LEAN_SRC_ROOT [--tex FILE ...] [--skip-mathlib]
                                    [--lines]
Exit status is 1 if any citation fails, 0 otherwise.
"""
import argparse, re, sys
from pathlib import Path

DEFAULT_TEX = ["docs/src/book/main.tex"]
KEYWORDS = r"(?:theorem|lemma|def|structure|abbrev|instance|class|inductive|opaque|axiom|noncomputable\s+def|irreducible_def)"


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


_cache = {}


def decl_lines(file, last):
    """Line numbers (1-based) where a declaration whose name ends in `last` is introduced."""
    key = file
    if key not in _cache:
        _cache[key] = file.read_text(encoding="utf-8", errors="replace").splitlines()
    pat = re.compile(r"(?:^|[\s@\]])" + KEYWORDS + r"\s+(?:[\w'.«»]*\.)?" + re.escape(last) + r"(?![\w'!?])")
    # structure/class fields (`  name : T`) are declarations too
    fpat = re.compile(r"^\s+(?:\(|\{)?" + re.escape(last) + r"(?:\s+[\w']+)*\s*:(?!=)")
    hits = [n for n, l in enumerate(_cache[key], 1) if pat.search(l) or fpat.search(l)]
    return hits


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("root", type=Path, help="Lean source root, e.g. TomasOrtega/RH extracted/lean/src")
    ap.add_argument("--tex", nargs="+", type=Path, default=[Path(p) for p in DEFAULT_TEX])
    ap.add_argument("--skip-mathlib", action="store_true", help="skip modules starting with Mathlib/Batteries/Std/Lean/Init")
    ap.add_argument("--lines", action="store_true", help="also sanity-check the cited line ranges")
    ap.add_argument("-q", "--quiet", action="store_true")
    a = ap.parse_args()

    total = skipped = 0
    errors = []
    for tex in a.tex:
        for line, args in parse_leanref_file(tex):
            total += 1
            where = f"{tex}:{line}"
            if args is None:
                errors.append(f"{where}: malformed \\leanref (could not read 3 arguments)")
                continue
            decl, mod, rng = args
            if a.skip_mathlib and mod.split(".")[0] in ("Mathlib", "Batteries", "Std", "Lean", "Init", "Aesop", "Qq"):
                skipped += 1
                continue
            f = a.root / (mod.replace(".", "/") + ".lean")
            if not f.is_file():
                errors.append(f"{where}: module not found: {mod}  (declaration {decl})")
                continue
            last = decl.split(".")[-1]
            hits = decl_lines(f, last)
            if not hits:
                errors.append(f"{where}: `{last}` is not declared in {mod}  (declaration {decl})")
                continue
            if a.lines:
                nums = [int(x) for x in re.findall(r"\d+", rng)]
                if not nums or not re.fullmatch(r"\d+(-\d+)?(,\d+(-\d+)?)*", rng):
                    errors.append(f"{where}: cannot parse line range `{rng}`")
                    continue
                nlines = len(_cache[f])
                if max(nums) > nlines + 1:  # tolerate a trailing-newline "line"
                    errors.append(f"{where}: cited lines {rng} exceed the {nlines} lines of {mod}")
                elif min(hits) > max(nums):
                    errors.append(f"{where}: `{last}` in {mod} is declared at line(s) {hits}, after cited {rng}")
    for e in errors:
        print("FAIL", e)
    print(f"{total} \\leanref checked, {skipped} skipped, {len(errors)} failed")
    return 1 if errors else 0


def parse_leanref_file(p):
    return parse_leanrefs(p)


if __name__ == "__main__":
    sys.exit(main())

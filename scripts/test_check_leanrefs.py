import sys, tempfile, unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import check_leanrefs as C

LEAN = '''namespace Foo
-- def commentedLine : Nat := 0
/- outer /- nested -/ def inBlock : Nat := 0 -/
/-- doc comment
def inDoc : Nat := 0 -/
theorem good : True := trivial
theorem leaf.child : True := trivial
def other (a : Nat)
    (binderLooks : Nat) : Nat := a
structure S (x : Nat) where
  realField : Nat
  other2 : Nat
def after (
    notAField : Nat) : Nat := 0
end Foo
'''


class T(unittest.TestCase):
    def run_one(self, decl, lean=LEAN, ref=True):
        with tempfile.TemporaryDirectory() as d:
            d = Path(d)
            (d / "src").mkdir()
            (d / "src" / "M.lean").write_text(lean)
            tex = d / "b.tex"
            tex.write_text(f"\\leanref{{{decl}}}{{M}}{{1--2}}\n" if ref else "no refs here\n")
            return C.check(d / "src", [tex])

    def ok(self, decl):
        total, _, errs = self.run_one(decl)
        self.assertEqual((total, errs), (1, []))

    def bad(self, decl):
        total, _, errs = self.run_one(decl)
        self.assertEqual(total, 1)
        self.assertEqual(len(errs), 1, errs)

    def test_good(self):
        self.ok("good")
        self.ok("Foo.good")
    def test_wrong_namespace(self):
        self.bad("Baz.good")
        self.bad("Bar.Foo.good")         # extra cited prefix: no suffix matching
        self.bad("good.good"); self.bad("Foo.Foo.good")
    def test_qualified_needs_full_name(self):
        self.bad("S.realField")          # field of Foo.S, cited without namespace
    def test_root(self):
        lean = "namespace Foo\ntheorem _root_.Top.t : True := trivial\nend Foo\n"
        for d, good in [("Top.t", True), ("_root_.Top.t", True), ("Foo.Top.t", False), ("Foo.t", False)]:
            _, _, errs = self.run_one(d, lean=lean)
            self.assertEqual(not errs, good, d)
    def test_root_unqualified(self):
        self.bad("_root_.good")          # Foo.good is not root-level
        lean = "theorem good : True := trivial\n"
        _, _, errs = self.run_one("_root_.good", lean=lean)
        self.assertEqual(errs, [])
    def test_noncomputable_section(self):
        lean = "namespace N\nnoncomputable section\ndef a := 1\nend\ntheorem t : True := trivial\nend N\n"
        _, _, errs = self.run_one("N.t", lean=lean)
        self.assertEqual(errs, [])
        _, _, errs = self.run_one("t", lean=lean.replace("namespace N", "namespace N2"))
        self.assertEqual(errs, [])
    def test_all_skipped(self):
        with tempfile.TemporaryDirectory() as d:
            tex = Path(d) / "b.tex"
            tex.write_text("\\leanref{a}{Mathlib.X}{1--2}")
            checked, skipped, errs = C.check(d, [tex], skip_mathlib=True)
            self.assertEqual((checked, skipped), (0, 1))
            self.assertTrue(errs)
    def test_commented_out(self):
        self.bad("commentedLine"); self.bad("inBlock"); self.bad("inDoc")
    def test_prefix_token(self):
        self.bad("child.leaf"); self.bad("Foo.leaf")  # only leaf.child is declared
        self.ok("Foo.leaf.child")
    def test_binder_not_field(self):
        self.bad("binderLooks"); self.bad("notAField")
    def test_structure_field(self):
        self.ok("Foo.S.realField"); self.ok("other2")
    def test_zero_refs(self):
        total, _, errs = self.run_one("x", ref=False)
        self.assertEqual(total, 0)
        self.assertTrue(errs)
    def test_missing_module(self):
        with tempfile.TemporaryDirectory() as d:
            tex = Path(d) / "b.tex"
            tex.write_text("\\leanref{a}{Nope}{1--2}")
            self.assertTrue(C.check(d, [tex])[2])
    def test_tex_quirks(self):
        with tempfile.TemporaryDirectory() as d:
            d = Path(d); (d / "M.lean").write_text("theorem a_b : True := trivial\n")
            tex = d / "b.tex"
            tex.write_text("\\leanref{a\\_\\allowbreak{}b}{M}{1--1}\n% \\leanref{zz}{M}{1--1}\n")
            self.assertEqual(C.check(d, [tex]), (1, 0, []))



class IndexFormat(unittest.TestCase):
    def run_idx(self, body, lean=LEAN, skip=False):
        with tempfile.TemporaryDirectory() as d:
            d = Path(d)
            (d / "src" / "A").mkdir(parents=True)
            (d / "src" / "A" / "M.lean").write_text(lean)
            tex = d / "b.tex"
            tex.write_text(body)
            st = {}
            r = C.check(d / "src", [tex], skip_mathlib=skip, stats=st)
            return r, st

    def entry(self, decl, mod="A.M", rng="1--2"):
        return "\\texttt{%s} (\\texttt{%s}, lines %s)\\\\\n" % (decl, mod, rng)

    def test_good_with_escapes(self):
        lean = "theorem my_thm : True := trivial\n"
        (c, s, e), st = self.run_idx(self.entry("my\\_\\allowbreak{}thm", "A.\\allowbreak{}M"), lean)
        self.assertEqual((c, s, e), (1, 0, []))
        self.assertEqual(st, {"leanref": [0, 0, 0], "index": [1, 0, 0]})

    def test_qualified_strict(self):
        (_, _, e), _ = self.run_idx(self.entry("Foo.good"))
        self.assertEqual(e, [])
        (_, _, e), _ = self.run_idx(self.entry("Bar.Foo.good"))
        self.assertEqual(len(e), 1)
        (_, _, e), _ = self.run_idx(self.entry("Baz.good"))
        self.assertEqual(len(e), 1)

    def test_missing_module_and_decl(self):
        (_, _, e), _ = self.run_idx(self.entry("Foo.good", "A.Nope"))
        self.assertIn("module not found", e[0])
        (_, _, e), _ = self.run_idx(self.entry("Foo.nope"))
        self.assertIn("not declared", e[0])

    def test_single_line_and_mixed_counts(self):
        body = self.entry("Foo.good", rng="5") + "\\leanref{Foo.good}{A.M}{1--2}\n"
        (c, s, e), st = self.run_idx(body)
        self.assertEqual((c, s, e), (2, 0, []))
        self.assertEqual(st, {"leanref": [1, 0, 0], "index": [1, 0, 0]})

    def test_skip_mathlib_and_all_skipped(self):
        body = self.entry("riemannZeta_one", "Mathlib.X.Y")
        (c, s, e), st = self.run_idx(body, skip=True)
        self.assertEqual((c, s), (0, 1))
        self.assertTrue(e)
        (c, s, e), st = self.run_idx(body + self.entry("Foo.good"), skip=True)
        self.assertEqual((c, s, e), (1, 1, []))
        self.assertEqual(st["index"], [1, 1, 0])

    def test_commented_out_and_malformed(self):
        (c, s, e), _ = self.run_idx("% " + self.entry("Foo.nope") + self.entry("Foo.good"))
        self.assertEqual((c, e), (1, []))
        (_, _, e), _ = self.run_idx("see \\texttt{Foo.good}, lines 1--2\n" + self.entry("Foo.good"))
        self.assertTrue(any("malformed" in x for x in e))

    def test_unmoduled_leanrefs_list_not_checked(self):
        body = "\\leanrefs{\\texttt{Foo.nope}}\n" + self.entry("Foo.good")
        (c, s, e), _ = self.run_idx(body)
        self.assertEqual((c, e), (1, []))

    def test_range_forms(self):
        for rng in ("7", "12--30", "1--2,4--5,7"):
            (c, _, e), st = self.run_idx(self.entry("Foo.good", rng=rng))
            self.assertEqual((c, e), (1, []), rng)
            self.assertEqual(st["index"], [1, 0, 0])

    def test_malformed_ranges(self):
        for rng in ("foo", "12--", "--12", "12-30", "1,", ",1", "1,,2", "1,2--", "12--30--40", ""):
            (c, _, e), st = self.run_idx(self.entry("Foo.good", rng=rng))
            self.assertEqual(c, 0, rng)
            self.assertEqual(st["index"], [0, 0, 1], rng)
            self.assertTrue(e and "malformed" in e[0], rng)

    def test_malformed_counted_separately(self):
        body = self.entry("Foo.good") + self.entry("Foo.good", rng="x") + "\\leanref{Foo.good}{A.M}{1--2}\n"
        (c, _, e), st = self.run_idx(body)
        self.assertEqual((c, len(e)), (2, 1))
        self.assertEqual(st, {"leanref": [1, 0, 0], "index": [1, 0, 1]})

    def test_decl_named_badrange_is_a_normal_name(self):
        lean = "theorem badrange : True := trivial\n"
        (c, _, e), st = self.run_idx(self.entry("badrange") + "\\leanref{badrange}{A.M}{1--2}\n", lean)
        self.assertEqual((c, e), (2, []))
        self.assertEqual(st, {"leanref": [1, 0, 0], "index": [1, 0, 0]})

    def test_badrange_decl_with_malformed_range_is_still_malformed(self):
        lean = "theorem badrange : True := trivial\n"
        (c, _, e), st = self.run_idx(self.entry("badrange", rng="x"), lean)
        self.assertEqual((c, len(e)), (0, 1))
        self.assertEqual(st["index"], [0, 0, 1])
        self.assertIn("declaration badrange", e[0])

if __name__ == "__main__":
    unittest.main()

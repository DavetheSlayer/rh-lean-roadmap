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
        self.ok("Bar.Foo.good")          # extra cited prefix is a dot-suffix match
    def test_wrong_namespace(self):
        self.bad("Baz.good")
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


if __name__ == "__main__":
    unittest.main()

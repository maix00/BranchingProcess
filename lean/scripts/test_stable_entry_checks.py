import importlib.util
from pathlib import Path
import tempfile
import unittest


SCRIPTS = Path(__file__).resolve().parent


def load_script(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / filename)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load {filename}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


imports = load_script("stable_import_check", "check-stable-small-deviation-imports.py")
axioms = load_script("lean_axiom_check", "check-lean-axioms.py")


class StableImportCheckTests(unittest.TestCase):
    def test_feedback_module_stems_are_forbidden(self):
        for name in (
            "Probability.Process.Stable.SmallDeviation.Blocks.Lower.FeedbackEntrance",
            "Probability.Process.Stable.SmallDeviation.Blocks.Lower.FeedbackTube",
            "Probability.Process.Stable.SmallDeviation.Blocks.Lower.FeedbackProbability",
        ):
            with self.subTest(name=name):
                self.assertIsNotNone(imports.forbidden_import_reason(name))

    def test_finite_time_entrance_is_allowed(self):
        self.assertIsNone(imports.forbidden_import_reason(
            "Probability.Process.Stable.SmallDeviation.Blocks.Lower.FiniteTimeEntrance"
        ))

    def test_subtree_rule_and_import_parser(self):
        self.assertIsNotNone(imports.forbidden_import_reason(
            "Probability.Process.Path.Skorokhod.Corridor.Support.Dense"
        ))
        self.assertEqual(
            imports.imported_modules(
                "import Foo.Bar\npublic import Baz.Quux\n-- import No.Parse\n"
            ),
            ["Foo.Bar", "Baz.Quux"],
        )

    def test_missing_entry_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            counts, issues = imports.inspect_entries(
                ["Public.Entry"], Path(directory)
            )
        self.assertFalse(counts)
        self.assertTrue(any("missing public entry module" in issue for issue in issues))

    def test_entry_graph_checks_transitive_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            entry = root / "Public" / "Entry.lean"
            dep = root / "Public" / "Dep.lean"
            entry.parent.mkdir(parents=True)
            entry.write_text("import Public.Dep\n")
            dep.write_text(
                "import Probability.Process.Stable.SmallDeviation.Blocks.Lower.FeedbackTube\n"
            )
            counts, issues = imports.inspect_entries(["Public.Entry"], root)
        self.assertEqual(counts["Public.Entry"], 2)
        self.assertTrue(any("FeedbackTube" in issue for issue in issues))


class LeanAxiomCheckTests(unittest.TestCase):
    def test_exact_allowlist(self):
        output = "depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        self.assertEqual(axioms.check_output(output, 1), [])

    def test_unexpected_axiom_is_rejected(self):
        output = "depends on axioms: [propext, Classical.choice, Quot.sound, sorryAx]\n"
        self.assertTrue(axioms.check_output(output, 1))


if __name__ == "__main__":
    unittest.main()

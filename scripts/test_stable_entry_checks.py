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

    def test_unit_time_all_indices_entrance_is_forbidden(self):
        self.assertIsNotNone(imports.forbidden_import_reason(
            "Probability.Process.Stable.SmallDeviation.Blocks.ShiftComparison.AllIndices"
        ))

    def test_escape_rate_layers_are_public_entries(self):
        for name in (
            "Probability.Process.Stable.Corridor.Law",
            "Probability.Process.Stable.SmallDeviation.EscapeRate",
            "Probability.Process.Stable.SmallDeviation.EscapeRate.Corridor",
            "Probability.Process.Stable.SmallDeviation.EscapeRate.Endpoint",
            "Probability.Process.Stable.SmallDeviation.EscapeRate.Law",
        ):
            with self.subTest(name=name):
                self.assertIn(name, imports.ENTRY_MODULES)

    def test_subtree_rule_and_import_parser(self):
        self.assertIsNotNone(imports.forbidden_import_reason(
            "Probability.Process.Path.Skorokhod.Corridor.Support.Dense"
        ))
        self.assertEqual(
            imports.imported_modules(
                "import Foo.Bar Extra.Module -- import No.Parse\n"
                "public import Baz.Quux\n"
            ),
            ["Foo.Bar", "Extra.Module", "Baz.Quux"],
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

    def test_general_attraction_module_has_no_branching_dependency(self):
        self.assertEqual(imports.inspect_general_layer_boundaries(), [])

    def test_general_layer_boundary_checks_transitive_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            entry = root / "Public" / "Entry.lean"
            dep = root / "Public" / "Dep.lean"
            entry.parent.mkdir(parents=True)
            entry.write_text("import Public.Dep\n")
            dep.write_text("import Probability.BranchingRandomWalk.Walk.Path.Basic\n")
            issues = imports.inspect_general_layer_boundaries(
                {"Public.Entry": ("Probability.BranchingRandomWalk",)}, root
            )
        self.assertTrue(any("Public.Dep -> Probability.BranchingRandomWalk" in issue
                            for issue in issues))

    def test_stable_characteristic_function_layers_avoid_levy_and_branching(self):
        boundaries = {
            "Probability.Distributions.Stable.CharacteristicFunction": (
                "Probability.Distributions.Stable.Exponent",
                "Probability.Distributions.Stable.LevyKhintchine",
                "Probability.Process.Stable.JumpModel",
                "Probability.BranchingRandomWalk",
                "Combinatorics.BranchingWalk",
            ),
            "Probability.Distributions.Stable.Attraction.CharacteristicFunction": (
                "Probability.Distributions.Stable.Exponent",
                "Probability.Distributions.Stable.LevyKhintchine",
                "Probability.Process.Stable.JumpModel",
                "Probability.BranchingRandomWalk",
                "Combinatorics.BranchingWalk",
            ),
        }
        self.assertEqual(imports.inspect_general_layer_boundaries(boundaries), [])


class LeanAxiomCheckTests(unittest.TestCase):
    def test_allowlist_is_a_ceiling_not_an_exact_requirement(self):
        output = "'Example.theorem' depends on axioms: [Classical.choice]\n"
        self.assertEqual(axioms.check_output(output, ["Example.theorem"]), [])

    def test_unexpected_axiom_is_rejected(self):
        output = "'Example.theorem' depends on axioms: [propext, sorryAx]\n"
        self.assertTrue(axioms.check_output(output, ["Example.theorem"]))

    def test_missing_duplicate_and_unexpected_declarations_are_reported(self):
        output = (
            "'Example.theorem' depends on axioms: [propext]\n"
            "'Example.theorem' depends on axioms: [Classical.choice]\n"
            "'Unexpected.theorem' depends on axioms: []\n"
        )
        issues = axioms.check_output(
            output, ["Example.theorem", "Missing.theorem"]
        )
        self.assertTrue(any("missing axiom reports" in issue for issue in issues))
        self.assertTrue(any("duplicate axiom reports" in issue for issue in issues))
        self.assertTrue(any("unexpected declaration reports" in issue for issue in issues))


if __name__ == "__main__":
    unittest.main()

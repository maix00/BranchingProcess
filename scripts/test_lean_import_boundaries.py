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


imports = load_script("lean_import_check", "check-lean-import-boundaries.py")
axioms = load_script("lean_axiom_check", "check-lean-axioms.py")


class ImportBoundaryCheckTests(unittest.TestCase):
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
                "module\n"
                "public import Baz.Quux\n"
                "meta import Meta.Module\n"
                "public meta import PublicMeta.Module\n"
                "import all Private.Module\n"
                "import\n  Multiline.Module\n"
                "/- outer comment\n"
                "import No.Block\n"
                "/- nested public meta import No.Nested -/\n"
                "-/\n"
                "import Actual.Module -- import No.Parse\n"
            ),
            [
                "Baz.Quux",
                "Meta.Module",
                "PublicMeta.Module",
                "Private.Module",
                "Multiline.Module",
                "Actual.Module",
            ],
        )

    def test_import_parser_rejects_incomplete_import(self):
        with self.assertRaises(imports.ImportParseError):
            imports.imported_modules("module\npublic meta import all\n")

    def test_lean_parser_reports_module_system_header(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with_module = root / "WithModule.lean"
            without_module = root / "WithoutModule.lean"
            with_module.write_text("module\npublic import Foo.Bar\n")
            without_module.write_text("import Foo.Bar\n")
            flags, issues = imports.parse_module_headers_from_paths(
                [with_module, without_module]
            )
        self.assertEqual(issues, [])
        self.assertTrue(flags[with_module.resolve()])
        self.assertFalse(flags[without_module.resolve()])

    def test_required_production_modules_use_module_header(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for module in imports.MODULE_SYSTEM_REQUIRED_MODULES:
                path = imports.source_path(module, root)
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("module\nimport Foo.Bar\n")
            missing = imports.source_path(imports.MODULE_SYSTEM_REQUIRED_MODULES[-1], root)
            missing.write_text("import Foo.Bar\n")
            count, issues = imports.inspect_required_module_headers(root)
        self.assertEqual(count, len(imports.MODULE_SYSTEM_REQUIRED_MODULES))
        self.assertEqual(len(issues), 1)
        self.assertIn(str(missing.relative_to(root)), issues[0])

    def test_same_line_extra_module_name_is_not_an_import(self):
        # Lean's grammar allows one module identifier per import command. A second
        # identifier is an invalid command, so the dependency parser must not
        # invent a second edge from it.
        self.assertEqual(
            imports.imported_modules("import Foo.Bar Extra.Module\n"),
            ["Foo.Bar"],
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

    def test_unit_interval_time_coordinates_avoid_probability_imports(self):
        for module in (
            "Topology.Order.UnitInterval.Time",
            "Topology.Order.UnitInterval.Rational",
        ):
            with self.subTest(module=module):
                self.assertEqual(
                    imports.GENERAL_LAYER_BOUNDARIES[module], ("Probability",)
                )

    def test_declared_general_layer_boundaries_pass(self):
        self.assertEqual(imports.inspect_general_layer_boundaries(), [])

    def test_process_random_walk_subtree_avoids_branching_layers(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            entry = root / "Probability" / "Process" / "RandomWalk" / "Path.lean"
            dep = root / "Shared" / "Dep.lean"
            entry.parent.mkdir(parents=True)
            dep.parent.mkdir(parents=True)
            entry.write_text("import Shared.Dep\n")
            dep.write_text("import Combinatorics.BranchingWalk.Walk.Basic\n")
            issues = imports.inspect_general_layer_boundaries(
                root=root,
                import_graph={
                    "Probability.Process.RandomWalk.Path": ["Shared.Dep"],
                    "Shared.Dep": ["Combinatorics.BranchingWalk.Walk.Basic"],
                },
            )
        self.assertTrue(any("Combinatorics.BranchingWalk" in issue for issue in issues))

    def test_additive_path_subtree_avoids_probability_and_branching_layers(self):
        forbidden = (
            "Probability.Process.RandomWalk.Path.Basic",
            "Combinatorics.BranchingWalk.Walk.Basic",
        )
        entries = (
            "Algebra.BigOperators.AdditivePath.Block",
            "Algebra.Order.BigOperators.AdditivePath",
        )
        for entry_module in entries:
            for dependency in forbidden:
                with self.subTest(entry=entry_module, dependency=dependency):
                    with tempfile.TemporaryDirectory() as directory:
                        root = Path(directory)
                        entry = root / Path(*entry_module.split(".")).with_suffix(".lean")
                        dep = root / "Shared" / "Dep.lean"
                        entry.parent.mkdir(parents=True)
                        dep.parent.mkdir(parents=True)
                        entry.write_text("import Shared.Dep\n")
                        dep.write_text(f"import {dependency}\n")
                        issues = imports.inspect_general_layer_boundaries(
                            root=root,
                            import_graph={
                                entry_module: ["Shared.Dep"],
                                "Shared.Dep": [dependency],
                            },
                        )
                    self.assertTrue(any(dependency in issue for issue in issues))

    def test_generic_mogulskii_path_classes_avoid_random_walk_layer(self):
        modules = (
            "Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Boundary",
            "Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Basic",
            "MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Energy",
            "MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Approximation",
            "Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.FiniteUnion",
            "Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.Approximation",
        )
        forbidden = "Probability.Process.RandomWalk.Path.Basic"
        for module in modules:
            with self.subTest(module=module):
                with tempfile.TemporaryDirectory() as directory:
                    root = Path(directory)
                    entry = root / Path(*module.split(".")).with_suffix(".lean")
                    dep = root / "Shared" / "Dep.lean"
                    entry.parent.mkdir(parents=True)
                    dep.parent.mkdir(parents=True)
                    entry.write_text("import Shared.Dep\n")
                    dep.write_text(f"import {forbidden}\n")
                    issues = imports.inspect_general_layer_boundaries(
                        root=root,
                        import_graph={
                            module: ["Shared.Dep"],
                            "Shared.Dep": [forbidden],
                        },
                    )
                self.assertTrue(any(forbidden in issue for issue in issues))

    def test_recently_lowered_measure_and_analysis_layers_are_protected(self):
        expected = {
            "Analysis.Asymptotics.Scale": ("Probability",),
            "Analysis.Asymptotics.InverseScale": ("Probability",),
            "Analysis.Asymptotics.BlockScale": ("Probability",),
            "MeasureTheory.Measure.LevyMeasure": ("Probability",),
            "MeasureTheory.Measure.CharacteristicFunction.Convolution": (
                "Probability",
            ),
            "MeasureTheory.Measure.CharacteristicFunction.PositiveDefinite": (
                "Probability",
            ),
        }
        for module, forbidden in expected.items():
            with self.subTest(module=module):
                self.assertEqual(imports.GENERAL_LAYER_BOUNDARIES[module], forbidden)

    def test_generic_path_measure_layers_avoid_process_imports(self):
        expected = {
            "MeasureTheory.Measure.CadlagPath.ContinuityTimes": ("Probability",),
            "MeasureTheory.Measure.CadlagPath.Support.Corridor": ("Probability",),
            "MeasureTheory.Measure.CadlagPath.FiniteDimensional.Dense": (
                "Probability",
            ),
            "MeasureTheory.Measure.CadlagPath.Tightness": ("Probability",),
            "MeasureTheory.Measure.CadlagPath.RangeCover": ("Probability",),
            "MeasureTheory.Measure.CadlagPath.Corridor.Weight": ("Probability",),
            "MeasureTheory.MeasurableSpace.ContinuousMap.Oscillation": (
                "Probability",
            ),
            "MeasureTheory.Measure.ContinuousMap.Oscillation": (
                "Probability",
            ),
            "Probability.ConvergenceInDistribution.ContinuousMap.Corridor": (
                "Probability.Process",
            ),
            "Probability.ConvergenceInDistribution.ContinuousMap.Oscillation": (
                "Probability.Process",
            ),
            "MeasureTheory.Measure.ContinuousMap.Tightness.Oscillation": (
                "Probability",
            ),
            "MeasureTheory.Measure.ContinuousMap.Tightness.Criteria": (
                "Probability",
            ),
            "MeasureTheory.Measure.Recurrence.BlockBounds": ("Probability",),
        }
        for module, forbidden in expected.items():
            with self.subTest(module=module):
                self.assertEqual(
                    imports.GENERAL_LAYER_BOUNDARIES[module], forbidden
                )

    def test_offspring_modules_are_covered_by_application_boundaries(self):
        for module in (
            "Probability.BranchingProcess.Offspring.Law",
            "Probability.BranchingProcess.Offspring.Map",
            "Probability.BranchingProcess.Offspring.Count",
            "Probability.BranchingProcess.Offspring.PointMeasure",
            "Probability.BranchingProcess.Offspring.FieldLaw",
        ):
            with self.subTest(module=module):
                self.assertEqual(
                    imports.GENERAL_LAYER_BOUNDARIES[module],
                    (
                        "Probability.BranchingRandomWalk",
                        "Probability.BranchingProcess.GaltonWatson",
                    ),
                )

    def test_general_layer_boundary_checks_transitive_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            entry = root / "Public" / "Entry.lean"
            dep = root / "Public" / "Dep.lean"
            entry.parent.mkdir(parents=True)
            entry.write_text("import Public.Dep\n")
            dep.write_text("import Probability.BranchingRandomWalk.Law\n")
            issues = imports.inspect_general_layer_boundaries(
                {"Public.Entry": ("Probability.BranchingRandomWalk",)}, root
            )
        self.assertTrue(any("Public.Dep -> Probability.BranchingRandomWalk" in issue
                            for issue in issues))

    def test_offspring_boundary_checks_transitive_galton_watson_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            entry = root / "Probability" / "BranchingProcess" / "Offspring" / "Law.lean"
            dep = root / "Shared" / "Dep.lean"
            entry.parent.mkdir(parents=True)
            dep.parent.mkdir(parents=True)
            entry.write_text("import Shared.Dep\n")
            dep.write_text("import Probability.BranchingProcess.GaltonWatson.Law\n")
            issues = imports.inspect_general_layer_boundaries(
                {
                    "Probability.BranchingProcess.Offspring.Law": (
                        "Probability.BranchingRandomWalk",
                        "Probability.BranchingProcess.GaltonWatson",
                    ),
                },
                root,
            )
        self.assertTrue(any("GaltonWatson" in issue for issue in issues))

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

    def test_cosine_defect_bridge_does_not_import_inverse_tauberian_layer(self):
        self.assertEqual(
            imports.inspect_general_layer_boundaries(
                {
                    "Probability.Distributions.CharacteristicFunction.Symmetrization.RegularVariation": (
                        "Probability.Distributions.CharacteristicFunction.Tauberian",
                        "Probability.Distributions.Stable.Attraction",
                        "Analysis.Fourier.CosineTauberian.Inversion",
                        "Analysis.Fourier.CosineTauberian.Mellin",
                    ),
                }
            ),
            [],
        )

    def test_probability_tauberian_adapters_avoid_unrelated_upper_layers(self):
        boundaries = {
            "Probability.Distributions.CharacteristicFunction.CosineDefect": (
                "Probability.Distributions.CharacteristicFunction.Tauberian",
                "Analysis.Fourier.CosineTauberian",
            ),
            "Probability.Distributions.CharacteristicFunction.Symmetrization.Tail": (
                "Probability.Distributions.CharacteristicFunction.Tauberian",
                "Analysis.Fourier.CosineTauberian.Inversion",
                "Analysis.Fourier.CosineTauberian.Mellin",
            ),
            "Probability.Distributions.CharacteristicFunction.Tauberian.SecondTail": (
                "Probability.Distributions.CharacteristicFunction.Tauberian.Kernel",
                "Probability.Distributions.Stable.Attraction",
                "Probability.BranchingRandomWalk",
                "Combinatorics.BranchingWalk",
            ),
        }
        self.assertEqual(imports.inspect_general_layer_boundaries(boundaries), [])

    def test_analysis_cosine_tauberian_layers_avoid_probability(self):
        boundaries = {
            "Analysis.Fourier.CosineTauberian.Kernel": ("Probability",),
            "Analysis.Fourier.CosineTauberian.Inversion": ("Probability",),
            "Analysis.Fourier.CosineTauberian.Mellin": ("Probability",),
            "Analysis.Fourier.CosineTauberian.RegularVariation": ("Probability",),
        }
        self.assertEqual(imports.inspect_general_layer_boundaries(boundaries), [])

    def test_poisson_general_layers_are_covered(self):
        for module in (
            "Probability.Distributions.Poisson.Basic",
            "Probability.RandomMeasure.Poisson.PointFamily",
            "Probability.RandomMeasure.Poisson.Basic",
            "Probability.RandomMeasure.Poisson.Integral",
        ):
            with self.subTest(module=module):
                self.assertIn(module, imports.GENERAL_LAYER_BOUNDARIES)

    def test_poisson_boundary_checks_transitive_process_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            entry = root / "Probability" / "RandomMeasure" / "Poisson" / "Integral.lean"
            dep = root / "Shared" / "Dep.lean"
            entry.parent.mkdir(parents=True)
            dep.parent.mkdir(parents=True)
            entry.write_text("import Shared.Dep\n")
            dep.write_text("import Probability.Process.Stable.JumpModel\n")
            issues = imports.inspect_general_layer_boundaries(
                {
                    "Probability.RandomMeasure.Poisson.Integral": (
                        "Probability.Process.Stable",
                    ),
                },
                root,
            )
        self.assertTrue(
            any("Shared.Dep -> Probability.Process.Stable" in issue for issue in issues)
        )


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
        self.assertTrue(any("missing axiom report" in issue for issue in issues))
        self.assertTrue(any("duplicate axiom reports" in issue for issue in issues))
        self.assertTrue(
            any("unexpected declaration reports" in issue for issue in issues)
        )


if __name__ == "__main__":
    unittest.main()

import importlib.util
import json
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch

from lean_test_registry import read_registry, registry_entries, expected_declarations

SCRIPTS = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('unified_checks', SCRIPTS / 'check.py')
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)


class VerificationTests(unittest.TestCase):
    def setUp(self):
        env = patch.dict('os.environ', {'GITHUB_REF': 'refs/heads/test', 'GITHUB_BASE_REF': ''})
        env.start()
        self.addCleanup(env.stop)

    def args(self, **kwargs):
        data = dict(scope='related', public_api=False, dependency_boundary=False,
                    merge_main=False, module=[], jobs=2, output_dir=Path('/tmp/check-test'))
        return SimpleNamespace(**(data | kwargs))

    def test_current_inventory_is_complete_and_categories_are_separate(self):
        checks.validate_inventory()
        self.assertEqual({e['category'] for e in registry_entries('required').values()}, {'required'})

    def test_required_inventory_does_not_read_advisory_manifests(self):
        with patch.object(Path, 'glob', side_effect=AssertionError('advisory metadata accessed')):
            checks.validate_inventory('required')

    def test_bad_advisory_inventory_does_not_block_required_registry(self):
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory) / 'registry.json'
            p.write_text(json.dumps({'schema_version': 1, 'allowed_axioms': [], 'entries': {
                'BranchingProcessTest/X.lean': {'category': 'required', 'declarations': ['x']},
                'LiteratureProofTest/Citation/X.lean': {'category': 'literature', 'declarations': ['x', 'x']}}}))
            read_registry(p, category='required')
            with self.assertRaises(ValueError):
                read_registry(p, category='literature')

    def test_wrong_category_cannot_make_advisory_a_required_test(self):
        path = 'LiteratureProofTest/Citation/Advisory.lean'
        with self.assertRaises(ValueError):
            expected_declarations(path, 'required')

    def test_registry_rejects_duplicate_declarations_and_path_escape(self):
        for path, declarations in [('BranchingProcessTest/X.lean', ['x', 'x']),
                                   ('BranchingProcessTest/../X.lean', ['x'])]:
            with tempfile.TemporaryDirectory() as directory:
                p = Path(directory) / 'registry.json'
                p.write_text(json.dumps({'schema_version': 1, 'allowed_axioms': [],
                    'entries': {path: {'category': 'required', 'declarations': declarations}}}))
                with self.assertRaises(ValueError):
                    read_registry(p)

    def test_theorem_proof_change_preserves_local_scope(self):
        old = 'theorem one : 1 = 1 := by rfl\n'
        new = 'theorem one : 1 = 1 := by decide\n'
        p = 'Analysis/Example.lean'
        self.assertEqual(checks.requires_full([p], {p: old}, {p: new}), [])
        self.assertEqual(checks.api_surface(old), checks.api_surface(
            old + 'private lemma helper : True := by trivial\n'))

    def test_unchanged_definition_does_not_escalate_adjacent_proof_edit(self):
        old = 'def value : ℕ := 1\n\nlemma one : 1 = 1 := by rfl\n'
        new = old.replace('by rfl', 'by decide')
        p = 'Analysis/Example.lean'
        self.assertEqual(checks.requires_full([p], {p: old}, {p: new}), [])
        self.assertTrue(checks.requires_full([p], {p: old}, {p: old.replace(':= 1', ':= 2')}))

    def test_public_semantics_and_boundaries_escalate(self):
        old = 'theorem one (x : ℕ) : x = x := by rfl\n'
        for new in ['theorem one (x : ℤ) : x = x := by rfl\n',
                    'import Analysis.Other\n' + old, '',
                    'public section\n' + old, '@[simp]\n' + old]:
            p = 'Analysis/Example.lean'
            self.assertTrue(checks.requires_full([p], {p: old}, {p: new}))
        p = 'Analysis/Example.lean'
        self.assertTrue(checks.requires_full([p], {p: 'def x := 1'}, {p: 'def x := 2'}))
        for p in ['scripts/helper.py', '.github/workflows/build.yml', 'Vendor/Mathlib', 'lean-toolchain']:
            self.assertTrue(checks.requires_full([p], {}, {}))

    def test_multiline_variable_context_is_part_of_public_surface(self):
        a = 'variable\n  {X : Type}\n\ntheorem same (x : X) : x = x := by rfl\n'
        b = a.replace('{X : Type}', '{X : Type} [Nonempty X]')
        self.assertNotEqual(checks.api_surface(a), checks.api_surface(b))

    def test_duplicate_registry_keys_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory) / 'registry.json'
            p.write_text('{"schema_version":1,"schema_version":1}')
            with self.assertRaises(ValueError):
                read_registry(p)

    def test_removed_module_reaches_stale_importers(self):
        graph = {'Analysis.Client': ['Analysis.Removed'],
                 'BranchingProcessTest.Client': ['Analysis.Client']}
        self.assertEqual(checks.affected_modules(['Analysis/Removed.lean'], graph),
                         {'Analysis.Removed', 'Analysis.Client', 'BranchingProcessTest.Client'})

    def test_explicit_module_includes_dependent_modules(self):
        graph = {'Analysis.Owner': [], 'Analysis.Client': ['Analysis.Owner']}
        scope, _, steps = checks.make_plan(self.args(module=['Analysis.Owner']), [], {}, {}, graph)
        self.assertEqual(scope, 'related')
        build = next(command for name, command in steps if name == 'build')
        self.assertIn('Analysis.Client', build)
        self.assertNotIn(['lake', 'build'], [c for _, c in steps])

    def test_full_override_and_literature_are_distinct(self):
        scope, _, steps = checks.make_plan(self.args(public_api=True), [], {}, {}, {})
        self.assertEqual(scope, 'full')
        self.assertNotIn('literature', [n for n, _ in steps])
        scope, _, steps = checks.make_plan(self.args(scope='literature'), [], {}, {}, {})
        self.assertEqual(scope, 'literature')
        self.assertEqual(len(steps), 1)

    def test_ci_has_one_front_door_and_no_expected_declaration_lists(self):
        required = (checks.ROOT / '.github/workflows/build.yml').read_text()
        advisory = (checks.ROOT / '.github/workflows/literature-proofs.yml').read_text()
        self.assertEqual(required.count('python3 scripts/check.py'), 1)
        self.assertNotIn('--expected', required)
        self.assertNotIn('run-all-lean-tests.py', required)
        self.assertIn('scripts/check.py --scope literature', advisory)
        self.assertIn('continue-on-error: true', advisory)

    def test_main_target_requires_full_checks(self):
        with patch.dict('os.environ', {'GITHUB_BASE_REF': 'main'}):
            scope, reasons, _ = checks.make_plan(self.args(), [], {}, {}, {})
        self.assertEqual(scope, 'full')
        self.assertIn('main integration', reasons)

    def test_empty_local_plan_does_not_claim_a_full_build(self):
        scope, reasons, steps = checks.make_plan(self.args(), [], {}, {}, {})
        self.assertEqual((scope, reasons, steps), ('related', [], []))


if __name__ == '__main__':
    unittest.main()

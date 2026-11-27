import importlib.util
from pathlib import Path
import subprocess
import tempfile
import tomllib
import unittest

SCRIPTS = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('literature_runner', SCRIPTS / 'run-literature-proof-tests.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class LiteratureProofRunnerTests(unittest.TestCase):
    def entry(self, name):
        return {'module': f'LiteratureProofTest.Citation.{name}', 'axioms': [name],
                'source_correspondence': 'Recorded reference steps and assumptions.'}

    def test_invalid_path_cannot_escape_advisory_root(self):
        for module in ['Probability.Result', 'LiteratureProofTest.Citation...Escape',
                       'LiteratureProofTest.Citation/Outside.Result']:
            with self.subTest(module=module), self.assertRaises(ValueError):
                runner.validated_entry_path(module)

    def test_failure_does_not_prevent_another_entry_from_reporting(self):
        calls = []

        def run(command, **kwargs):
            calls.append(command)
            if command[:2] == ['lake', 'build'] and command[-1].endswith('.Broken'):
                return subprocess.CompletedProcess(command, 1, 'compile failure', '')
            if command[:2] == ['lake', 'build']:
                return subprocess.CompletedProcess(command, 0, '', '')
            return subprocess.CompletedProcess(command, 0,
                "'Good' depends on axioms: [propext, Classical.choice, Quot.sound]\n", '')

        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            failed = runner.check_entry(self.entry('Broken'), output, run)
            passed = runner.check_entry(self.entry('Good'), output, run)
            self.assertEqual(failed['status'], 'compilation_failed')
            self.assertEqual(passed['status'], 'mechanical_checks_passed')
            self.assertIn('compile failure', Path(failed['log']).read_text())
        self.assertEqual(len(calls), 3)

    def test_unproved_axiom_is_reported_even_when_lean_compiles(self):
        def run(command, **kwargs):
            return subprocess.CompletedProcess(command, 0,
                "'Bad' depends on axioms: [sorryAx]\n", '')

        with tempfile.TemporaryDirectory() as directory:
            result = runner.check_entry(self.entry('Bad'), Path(directory), run)
        self.assertEqual(result['status'], 'axiom_audit_failed')

    def test_advisory_library_is_not_a_default_build_target(self):
        config = tomllib.loads((runner.ROOT / 'lakefile.toml').read_text())
        self.assertNotIn('LiteratureProofTest', config['defaultTargets'])
        self.assertTrue(any(lib['name'] == 'LiteratureProofTest' for lib in config['lean_lib']))
        workflow = (runner.ROOT / '.github/workflows/literature-proofs.yml').read_text()
        self.assertIn('continue-on-error: true', workflow)
        self.assertNotIn('needs:', workflow)


if __name__ == '__main__':
    unittest.main()

"""Check cache writer isolation and post-verification persistence without a CI VM."""

import os
from pathlib import Path
import re
import subprocess
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
ACTION = ROOT / '.github/actions/prepare-lean/action.yml'


class WorkspaceCacheTests(unittest.TestCase):
    def test_cache_keys_separate_writers_and_prioritize_same_source_required_build(self):
        source = ACTION.read_text()
        script = textwrap.dedent(re.search(r'      run: \|\n(.*?)(?=    - name:)', source, re.S)[1])
        outputs = {}
        with tempfile.TemporaryDirectory() as directory:
            for category in ['required', 'advisory']:
                output = Path(directory) / category
                env = dict(os.environ, CACHE_CATEGORY=category, TOOLCHAIN_HASH='toolchain',
                           MANIFEST_HASH='manifest', RUNNER_OS='Linux', RUNNER_ARCH='X64',
                           GITHUB_SHA='source-sha', GITHUB_OUTPUT=str(output))
                subprocess.run(['bash', '-c', script], cwd=ROOT, env=env, check=True, capture_output=True)
                outputs[category] = output.read_text().splitlines()
        required_key = outputs['required'][0].removeprefix('key=')
        advisory_key = outputs['advisory'][0].removeprefix('key=')
        self.assertNotEqual(required_key, advisory_key)
        self.assertIn('-required-', required_key)
        self.assertIn('-advisory-', advisory_key)
        self.assertEqual(outputs['advisory'][2], required_key)
        self.assertTrue(required_key.endswith('-source-sha'))

    def test_early_lean_action_cache_save_is_disabled(self):
        source = ACTION.read_text()
        self.assertIn('use-github-cache: false', source)
        self.assertNotIn('actions/cache/save@', source)
        self.assertIn('Vendor/Mathlib rev-parse HEAD', source)
        self.assertIn('Vendor/BrownianMotion rev-parse HEAD', source)

    def test_workflows_save_verified_workspaces_after_their_checks(self):
        for file, check_name, category in [
            ('build.yml', 'Unified required checks', 'required'),
            ('literature-proofs.yml', 'Compile and audit reference proofs', 'advisory'),
        ]:
            with self.subTest(workflow=file):
                source = (ROOT / '.github/workflows' / file).read_text()
                self.assertIn('uses: ./.github/actions/prepare-lean', source)
                self.assertIn(f'category: {category}', source)
                self.assertLess(source.index(check_name), source.index('uses: actions/cache/save@v5'))
                self.assertIn("steps.checks.outcome == 'success'", source)
                self.assertIn('key: ${{ steps.workspace.outputs.cache-key }}', source)
        advisory = (ROOT / '.github/workflows/literature-proofs.yml').read_text()
        self.assertNotIn('needs:', advisory)
        self.assertNotIn('workflow_run:', advisory)
        self.assertIn('continue-on-error: true', advisory)


if __name__ == '__main__':
    unittest.main()

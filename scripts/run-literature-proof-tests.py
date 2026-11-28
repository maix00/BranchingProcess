#!/usr/bin/env python3
"""Report reference-proof checks separately from required production regressions."""

import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from lean_test_registry import expected_declarations

ROOT = Path(__file__).resolve().parents[1]
PROOF_ROOT = Path('LiteratureProofTest')


def load_axiom_checker():
    spec = importlib.util.spec_from_file_location('literature_axioms', ROOT / 'scripts/check-lean-axioms.py')
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    return checker


def validated_entry_path(module):
    parts = module.split('.')
    if len(parts) < 3 or parts[0] != 'LiteratureProofTest' or not all(
        re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', part) for part in parts
    ):
        raise ValueError(f'Invalid literature test module: {module!r}')
    return Path(*parts).with_suffix('.lean')


def check_entry(entry, output_dir, run=subprocess.run):
    """A failed entry is reported; callers continue with the other references."""
    module = entry['module']
    path = validated_entry_path(module)
    expected = expected_declarations(path, 'literature')
    if not expected:
        raise ValueError(f'{module}: at least one named axiom audit is required')
    log = output_dir / path.with_suffix('.log')
    log.parent.mkdir(parents=True, exist_ok=True)
    build = run(['lake', 'build', module], cwd=ROOT, capture_output=True, text=True)
    log.write_text(build.stdout + build.stderr)
    result = {'module': module, 'log': str(log), 'source_correspondence': entry['source_correspondence'],
              'source_review_status': entry.get('source_review_status', 'unreviewed')}
    if build.returncode:
        return {**result, 'status': 'compilation_failed', 'returncode': build.returncode}
    compiled = run(['lake', 'env', 'lean', str(path)], cwd=ROOT, capture_output=True, text=True)
    with log.open('a') as stream:
        stream.write('\nFresh entry compilation and named axiom audit:\n')
        stream.write(compiled.stdout + compiled.stderr)
    if compiled.returncode:
        return {**result, 'status': 'compilation_failed', 'returncode': compiled.returncode}
    issues = load_axiom_checker().check_output(compiled.stdout, expected)
    return {**result, 'status': 'axiom_audit_failed' if issues else 'mechanical_checks_passed',
            'axiom_issues': issues, 'audited_declarations': expected}


def revision(command):
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    return result.stdout.strip() if not result.returncode else 'unavailable'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=ROOT / '.lake/literature-proof-reports')
    args = parser.parse_args()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    reports = []
    for path in sorted((ROOT / PROOF_ROOT).glob('*/manifest.json')):
        data = json.loads(path.read_text())
        if data.get('schema_version') != 1:
            raise ValueError(f'Unsupported literature manifest: {path}')
        for entry in data['entries']:
            result = check_entry(entry, output)
            reports.append({**result, 'reference': data['reference'], 'manifest': str(path.relative_to(ROOT))})
            print(f"{result['status']}: {entry['module']}", flush=True)
    metadata = {'commit': revision(['git', 'rev-parse', 'HEAD']),
                'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
                'mathlib': revision(['git', '-C', 'Vendor/Mathlib', 'rev-parse', 'HEAD'])}
    (output / 'report.json').write_text(json.dumps({'environment': metadata, 'results': reports}, indent=2) + '\n')
    lines = ['# Literature-proof tests (advisory)', '',
             'These checks are not merge requirements. Mechanical success is evidence only',
             'for the stated Lean argument; consult each recorded source correspondence.', '',
             f"Commit: `{metadata['commit']}`; toolchain: `{metadata['toolchain']}`.", '']
    for report in reports:
        lines += [f"- `{report['module']}`: **{report['status']}**.",
                  f"  Source review: `{report['source_review_status']}`. {report['source_correspondence']}"]
    if not reports:
        lines.append('No literature-proof entries were discovered.')
    summary = '\n'.join(lines) + '\n'
    (output / 'report.md').write_text(summary)
    if os.environ.get('GITHUB_STEP_SUMMARY'):
        with open(os.environ['GITHUB_STEP_SUMMARY'], 'a') as stream:
            stream.write(summary)
    return int(not reports or any(r['status'] != 'mechanical_checks_passed' for r in reports))


if __name__ == '__main__':
    sys.exit(main())

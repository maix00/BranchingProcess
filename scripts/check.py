#!/usr/bin/env python3
"""Unified, measured checks: affected modules by default, full at public boundaries."""

import argparse
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import resource
import subprocess
import sys
import time

from lean_test_registry import ROOT, registry_entries

PRODUCTION_ROOTS = {'Algebra', 'Analysis', 'Combinatorics', 'LinearAlgebra',
                    'MeasureTheory', 'Order', 'Probability', 'Topology'}


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()


def module_name(path):
    return '.'.join(Path(path).with_suffix('').parts)


def api_surface(source):
    """Conservative source comparison, not a Lean parser or a semantic proof."""
    source = re.sub(r'/\-.*?\-/', '', source, flags=re.S)
    source = re.sub(r'--[^\n]*', '', source)
    signatures = re.findall(
        r'(?ms)^[ \t]*(?:@\[[^\]]*\][ \t\r\n]*)*(?:(?:private|protected|public|noncomputable|unsafe)\s+)*'
        r'(?:def|abbrev|lemma|theorem|structure|class|inductive|instance|opaque|axiom)\b'
        r'.*?(?=:=|\bwhere\b|\Z)', source)
    signatures = [s for s in signatures if not re.match(
        r'\s*(?:@\[[^\]]*\]\s*)*private\b', s)]
    contexts = re.findall(r'(?m)^[ \t]*(?:namespace|section|open)\b.*$', source)
    contexts += re.findall(r'(?m)^[ \t]*@\[[^\]]*\]', source)
    contexts += re.findall(r'(?ms)^[ \t]*(?:variable|universe|local notation|notation|attribute|set_option)\b.*?(?=\n\s*\n|\Z)', source)
    return [' '.join(s.split()) for s in signatures + contexts]


def definition_surface(source):
    """Compare definition blocks without treating adjacent proof edits as changes."""
    source = re.sub(r'/\-.*?\-/', '', source, flags=re.S)
    source = re.sub(r'--[^\n]*', '', source)
    starts = list(re.finditer(
        r'(?m)^[ \t]*(?:@\[[^\]]*\][ \t\r\n]*)*(?:(?:private|protected|public|noncomputable|unsafe)\s+)*'
        r'(?P<kind>def|abbrev|lemma|theorem|structure|class|inductive|instance|opaque|axiom)\b', source))
    return [source[m.start():starts[i+1].start() if i+1 < len(starts) else len(source)].strip()
            for i, m in enumerate(starts) if m['kind'] not in {'lemma', 'theorem'}]


def requires_full(changed, before, after):
    reasons = []
    for path in changed:
        p = Path(path)
        if (p.parts and p.parts[0] in {'scripts', '.github', 'Vendor'}) or p.name in {
            'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', '.gitmodules'}:
            reasons.append(f'check/dependency boundary: {path}')
        elif p.suffix == '.lean' and p.parts[0] in PRODUCTION_ROOTS:
            old, new = before.get(path, ''), after.get(path, '')
            imports = lambda s: re.findall(r'(?m)^(?:public )?import (?:all )?.+$', s)
            # Renames, module visibility, declaration signatures and imports are
            # API boundaries. Definition bodies can also change mathematical objects.
            if (not old or not new or api_surface(old) != api_surface(new)
                    or imports(old) != imports(new)
                    or re.findall(r'(?m)^(?:module|.*public section|.*expose.*)$', old)
                    != re.findall(r'(?m)^(?:module|.*public section|.*expose.*)$', new)
                    or definition_surface(old) != definition_surface(new)):
                reasons.append(f'public API or dependency change: {path}')
    return reasons


def affected_modules(changed, graph):
    reverse = {}
    for caller, deps in graph.items():
        for dep in deps:
            reverse.setdefault(dep, set()).add(caller)
    seen, pending = set(), [module_name(p) for p in changed if p.endswith('.lean')]
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        pending.extend(reverse.get(name, ()))
    return seen


def validate_inventory(category='required'):
    entries = registry_entries(category)
    if category == 'required':
        actual = {p for p in git('ls-files', '--cached', '--others', '--exclude-standard',
                                  '--', 'BranchingProcessTest').splitlines()
                  if p.endswith('.lean') and (ROOT / p).is_file()}
        expected = {p for p, e in entries.items() if e['category'] == 'required'}
        if actual != expected:
            raise ValueError(f'Required registry drift: missing={expected-actual}, unregistered={actual-expected}')
        return
    manifested = set()
    for manifest in ROOT.glob('LiteratureProofTest/*/manifest.json'):
        data = json.loads(manifest.read_text())
        for entry in data['entries']:
            if 'axioms' in entry:
                raise ValueError(f'Duplicate axiom inventory in {manifest}')
            path = entry['module'].replace('.', '/') + '.lean'
            if path in manifested:
                raise ValueError(f'Duplicate literature entry: {path}')
            manifested.add(path)
    literature = {p for p, e in entries.items() if e['category'] == 'literature'}
    if manifested != literature or any(not (ROOT / p).is_file() for p in literature):
        raise ValueError('Literature manifests and central registry disagree')


def change_data(base, explicit):
    prefix = git('rev-parse', '--show-prefix')
    if base:
        paths = git('diff', '--name-only', '--relative', base, '--').splitlines()
    else:
        paths = git('diff', '--name-only', '--relative', 'HEAD', '--').splitlines()
    paths += git('ls-files', '--others', '--exclude-standard').splitlines()
    paths = sorted(set(paths + explicit))
    before, after = {}, {}
    for p in paths:
        before[p], after[p] = '', ''
        if p.endswith('.lean'):
            result = subprocess.run(['git', 'show', f'{base or "HEAD"}:{prefix}{p}'],
                                    cwd=ROOT, capture_output=True, text=True)
            before[p] = result.stdout if not result.returncode else ''
            after[p] = (ROOT / p).read_text() if (ROOT / p).is_file() else ''
    return paths, before, after


def make_plan(args, changed, before, after, graph):
    reasons = requires_full(changed, before, after)
    if args.public_api or args.dependency_boundary or args.merge_main:
        reasons.append('explicit public API, dependency, or main-merge check')
    if os.environ.get('GITHUB_REF') == 'refs/heads/main' or os.environ.get('GITHUB_BASE_REF') == 'main':
        reasons.append('main integration')
    scope = 'full' if args.scope == 'full' or reasons else 'related'
    if args.scope == 'literature':
        return 'literature', [], [('literature', [sys.executable, 'scripts/run-literature-proof-tests.py',
                                                '--output-dir', str(args.output_dir / 'literature')])]
    steps = []
    if scope == 'full':
        steps = [('tooling', [sys.executable, '-m', 'unittest', 'discover', '-s', 'scripts', '-p', 'test_*.py']),
                 ('visualizers', ['node', 'scripts/check-visualizer-manifest.mjs']),
                 ('build', ['lake', 'build']),
                 ('regressions', [sys.executable, 'scripts/run-all-lean-tests.py', '--jobs', str(args.jobs),
                                  '--output-dir', str(args.output_dir / 'lean-tests')]),
                 ('imports', [sys.executable, 'scripts/check-lean-import-boundaries.py']),
                 ('style', [sys.executable, 'scripts/run-mathlib-lint-style.py'])]
    else:
        affected = affected_modules(changed + [n.replace(".", "/") + ".lean" for n in args.module], graph)
        modules = sorted(n for n in affected if n in graph and n.split('.')[0] in PRODUCTION_ROOTS)
        tests = sorted(p for p, e in registry_entries('required').items()
                       if e['category'] == 'required' and module_name(p) in affected)
        if modules:
            steps.append(('build', ['lake', 'build', *modules]))
        if tests:
            steps.append(('regressions', [sys.executable, 'scripts/run-all-lean-tests.py', '--jobs', str(args.jobs),
                                         '--output-dir', str(args.output_dir / 'lean-tests'),
                                         *[arg for p in tests for arg in ('--test', p)]]))
        if modules:
            steps.append(('style', ['lake', 'exe', 'lint-style', *modules]))
    return scope, reasons, steps


def main():
    started = time.perf_counter()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scope', choices=['related', 'full', 'literature'], default='related')
    parser.add_argument('--base', help='compare changes to this Git revision')
    parser.add_argument('--changed', action='append', default=[], help='additional changed path relative to Lean root')
    parser.add_argument('--module', action='append', default=[], help='additional affected module')
    for flag in ('public-api', 'dependency-boundary', 'merge-main', 'dry-run'):
        parser.add_argument('--' + flag, action='store_true')
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--output-dir', type=Path, default=ROOT / '.lake/check-reports')
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    os.chdir(ROOT)
    args.output_dir = args.output_dir.resolve()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    validate_inventory('literature' if args.scope == 'literature' else 'required')
    if args.base is not None and (not args.base or set(args.base) == {'0'} or subprocess.run(
            ['git', 'cat-file', '-e', args.base + '^{commit}'], capture_output=True).returncode):
        args.base = None
        args.scope = 'full' if args.scope != 'literature' else 'literature'
    changed, before, after = change_data(args.base, args.changed)
    spec = importlib.util.spec_from_file_location('import_boundaries', ROOT / 'scripts/check-lean-import-boundaries.py')
    imports = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(imports)
    graph, _ = imports.load_import_graph(ROOT, include_advisory=args.scope == "literature")
    scope, reasons, steps = make_plan(args, changed, before, after, graph)
    unknown = set(args.module) - set(graph)
    if unknown:
        parser.error(f'Unknown local modules: {sorted(unknown)}')
    report = {'commit': git('rev-parse', 'HEAD'), 'dirty': bool(git('status', '--porcelain')),
              'scope': scope, 'reasons': reasons, 'changed': changed,
              'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
              'mathlib': git('-C', 'Vendor/Mathlib', 'rev-parse', 'HEAD'),
              'platform': platform.platform(), 'jobs': args.jobs,
              'planning_wall_seconds': time.perf_counter() - started,
              'lean_threads': os.environ.get('LEAN_NUM_THREADS', '2'),
              'cache_state': 'not measured; inspect build logs and CI cache restore steps', 'steps': []}
    print(json.dumps({'scope': scope, 'reasons': reasons, 'commands': steps}, indent=2), flush=True)
    if args.dry_run:
        return 0
    env = dict(os.environ)
    env.setdefault('LEAN_NUM_THREADS', '2')
    result = 1
    try:
        for name, command in steps:
            log = args.output_dir / f'{name}.log'
            start, cpu = time.perf_counter(), resource.getrusage(resource.RUSAGE_CHILDREN)
            with log.open('w') as stream:
                proc = subprocess.run(command, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
            end_cpu = resource.getrusage(resource.RUSAGE_CHILDREN)
            duration = time.perf_counter() - start
            report['steps'].append({'name': name, 'command': command, 'returncode': proc.returncode,
                                    'wall_seconds': duration,
                                    'child_cpu_seconds': end_cpu.ru_utime + end_cpu.ru_stime - cpu.ru_utime - cpu.ru_stime,
                                    'log': str(log)})
            print(f'{name}: exit {proc.returncode}, {duration:.2f}s; {log}', flush=True)
            if proc.returncode:
                result = proc.returncode
                break
        else:
            result = 0
    finally:
        report['returncode'] = result
        report['total_wall_seconds'] = time.perf_counter() - started
        (args.output_dir / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        summary = f'Checks: {scope}; commit {report["commit"]}; dirty={report["dirty"]}\n\n'
        summary += (f'Planning: {report["planning_wall_seconds"]:.2f}s; '
                    f'total wall: {report["total_wall_seconds"]:.2f}s.\n\n')
        summary += '\n'.join(f'- {s["name"]}: exit {s["returncode"]}, {s["wall_seconds"]:.2f}s wall, '
                             f'{s["child_cpu_seconds"]:.2f}s child CPU' for s in report['steps']) + '\n'
        (args.output_dir / 'report.md').write_text(summary)
        if os.environ.get('GITHUB_STEP_SUMMARY'):
            with open(os.environ['GITHUB_STEP_SUMMARY'], 'a') as stream:
                stream.write(summary)
    return result


if __name__ == '__main__':
    sys.exit(main())

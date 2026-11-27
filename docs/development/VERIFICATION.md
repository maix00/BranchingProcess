# Verification selection and measurements

Run commands from the Lean repository root (`docs/lean` in the dissertation
checkout), so elan selects its pinned `lean-toolchain` before Lake starts.
The single front door is `python3 scripts/check.py`.

| Change | Command / scope |
| --- | --- |
| Local proof-body change | Default affected checks; reverse imports select dependent production modules and required tests. |
| Explicit subject, clean tree | `python3 scripts/check.py --module Analysis.Asymptotics.Sequence.CubicScale` selects that owner and its current dependent modules/tests. |
| Public signatures/objects, imports, module visibility, dependency or check infrastructure | Full required checks. The conservative detector escalates automatically; use `--public-api` or `--dependency-boundary` for semantic changes the source comparison cannot recognize. |
| Integrating main | `python3 scripts/check.py --merge-main`; CI also detects pushes to main and PRs targeting main. |
| Preserved source argument | `python3 scripts/check.py --scope literature`; separate advisory workflow, never a dependency of required checks. |
| Explicit full regression | `python3 scripts/check.py --scope full` |
| Inspect selection without compiling | Add `--dry-run`; use `--base REV` for a committed range or repeat `--changed PATH` for additional paths. |

Without `--base`, compare tracked changes to HEAD and include nonignored new
files. CI compares to the PR base or previous push. Missing/zero/unavailable CI
bases select full checks. Removed modules remain seeds in reverse-import
selection, so stale clients fail rather than being silently omitted. Source
comparison is a conservative convenience, not a Lean parser or proof of semantic
equivalence. Maintainers must flag meaning-changing public changes even when
signatures are textually unchanged. An explicit local scope cannot override an
automatic required full-check decision. No changes or only prose changes can
legitimately produce no Lean build; this is reported as an empty plan, not a
claim that production was rebuilt.

Full checks execute tooling tests, visualizer-manifest validation, one default
production build, required Lean regressions with axiom verification, import
boundaries and Mathlib style lint. Production globs include every production
source root. There are no duplicate declaration lists or repeated groups of
build targets in CI YAML. Related checks execute the affected build, selected
registered regressions and their style checks. New/removed tests still require
registry reconciliation in their own check category before that scope runs.
Required checks do not parse advisory manifests or validate advisory entry
inventories; those diagnostics belong to the non-blocking literature scope.

## One axiom registry, two check categories

`scripts/lean-test-registry.json` owns allowed axioms and the explicit expected
reports for every required test and manifested literature entry. Empty lists
are explicit: an unexpected report is still rejected. There is no fallback
that silently accepts whatever declarations happen to remain in a test file.
The shared checker rejects missing, extra, duplicate, ambiguous and unapproved
reports. Shared JSON syntax and the allowed-axiom policy are common check
infrastructure; individual advisory entry/proof failures belong to their own scope. The ordinary test runner and advisory runner consume the same registry.
Literature manifests own bibliographic and source-correspondence metadata only.

When adding a test, register its path, category and reviewed expected declarations.
Keep `#print axioms` commands in its Lean entry. A registry update is reviewable
mathematical evidence; do not generate expected output from the current compiler
log merely to make a failing check pass. The initial consolidation retained the
previous reviewed lists and previous source-print inventories, and checked that
every former CI expected declaration remained represented.

Required regressions must not import literature tests. Advisory failures remain
visible through their process exit, per-entry status and retained logs, while
the dedicated CI job uses `continue-on-error: true`. Do not add that job to branch
protection, required aggregates, or required `needs`. The subtree publication
script watches only `build.yml`.

## Measure before optimizing

Each execution writes `report.json`, `report.md` and per-step logs under
`.lake/check-reports` (or `--output-dir`). Reports include the commit, dirty
state, toolchain, Mathlib revision, platform, worker/thread settings, actual
commands, exit statuses, planning and total wall time, per-step elapsed wall
seconds and aggregate child CPU seconds.
CPU times include waited-for subprocess children; they are not peak-memory or
per-core profiles. Cache hit/miss is not inferred from Lake task counts:
consult CI cache restore results and compiler logs, and record cold versus warm
runs when comparing performance. An empty plan has no performance evidence for
a build. Compare equivalent scopes and environments before changing concurrency,
caches or proof/module architecture. Preserve failure diagnostics in every run.

The required CI uploads these reports and uses the same front door; the advisory
CI uses `--scope literature` and retains its independent report. Check failures
are reported without weakening mathematical hypotheses or axiom policy.

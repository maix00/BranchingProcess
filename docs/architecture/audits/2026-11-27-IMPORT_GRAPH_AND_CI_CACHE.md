# Owned import graphs and independent CI caches

This review follows the compliance repair at source commit `130a89425` and
preflight `34644f37ab7d26772650c56348af70345959eb5b`. No mathematical Lean
statement, proof, hypothesis, LaTeX source or dependency pin is changed.

## Verified remote baseline

The baseline SHA's two workflows completed successfully, including every step:

- [Required run 45938051258](https://github.com/maix00/BranchingProcess/actions/runs/45938051258).
- [Advisory run 45938051308](https://github.com/maix00/BranchingProcess/actions/runs/45938051308).

The uploaded `required-check-reports` and `literature-proof-reports` artifacts were
retrieved rather than inferred from Lake task counts. They identify Linux x86_64,
Lean `v4.36.0-rc2`, Mathlib `26573066084e6e2aa8526ea358bc43b66d96f970`, four
required workers/two advisory workers and `LEAN_NUM_THREADS=2`.

| Observed metric | Required | Advisory |
| --- | ---: | ---: |
| Job elapsed, GitHub job start to completion | 446 s | 258 s |
| Checkout, step timestamps | 25 s | 11 s |
| Mathlib cache restore, step timestamps | 31 s | 31 s |
| Lean installation/workspace restoration, step timestamps | 49 s | 47 s |
| Unified checks, uploaded report total wall | 317.08 s | 163.72 s |
| Planning, within that report total | 7.84 s | 8.81 s |

Within required checks: tooling 38.75 s, visualizers 2.09 s, production build
107.05 s, regressions 123.70 s, import boundaries 8.03 s and style 29.61 s.
The advisory proof subprocess took 154.91 s. Preparation times are not subtracted
from these check totals: they are separate job steps. The jobs execute in parallel,
so adding their elapsed times is not the workflow critical-path time. A successful
cache-restore step alone does not identify its exact-hit/fallback/miss state.

## Confirmed scope defect and bounded graph change

The old `root.rglob` traversal included 9,412 vendor modules. Its graph had 11,394
nodes, many with `Vendor.*` names that were not the module names in local imports.
The new traversal prunes dependency/cache directories before descending. It keeps
1,982 owned nodes, including required tests and the Lean header utility, with
external imports retained as terminal edges. Both native-parser passes reported
zero errors. The required/advisory boundary guard remains enabled.

One local before/after observation on the same existing workspace took 10.89 s
and 5.12 s respectively. These single measurements are not a whole-CI benchmark
or a stable speedup estimate. Full and advisory planning no longer parse a graph
that their plans do not use; full verification still checks import boundaries.
Related-header parsing failure escalates to full verification instead of silently
using an incomplete reverse graph.

## Cache preparation decision

The official [lean-action v1 implementation](https://github.com/leanprover/lean-action/blob/v1/action.yml)
restores and saves `.lake` inside the composite action. With `build/test/lint`
disabled and manual checks following that action, the save happens before the
manual build and proof checks. Thus that save cannot retain the build products
created later in the same run. This is a lifecycle issue, distinct from the
unavoidable setup work on two independent hosted runners.

The shared preparation action disables that early internal cache operation.
Explicit restore keys distinguish required/advisory writers and identify the
source and pinned dependencies; explicit workflow saves occur only after the
respective checks succeed. An advisory run may reuse completed required output
or a compatible prior dependency seed without a job dependency or waiting loop.
The cache remains an optimization: current-source build traces and axiom checks
are always evaluated. The existing separate Mathlib cache/artifact behavior is
preserved. No duplicate theorem inventory or new mathematical gate is introduced.

## Evidence standard

The baseline timings above do not show the new configuration is faster. Record
the new exact SHA's completed CI and its uploaded report, including first-run
cache preparation/persistence costs. Further warm runs must be labeled separately.
Tests cover directory pruning while retaining external edges, skipped planning
scans, safe escalation on parse errors, distinct cache writers, same-source reuse
priority and cache persistence after successful checks. No performance percentage
is inferred from file counts, YAML size or passing tests.

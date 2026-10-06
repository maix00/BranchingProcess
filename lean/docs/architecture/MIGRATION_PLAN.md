# Architecture migration status

This records the structural migration of general measure, deterministic,
stopping-time, Poisson, and branching interfaces. The status is checked
against the source tree at the repository revision carrying this document.
It does not claim that the separate open limit-theorem obligations in
[`FORMALIZATION_CHECKLIST.md`](../../FORMALIZATION_CHECKLIST.md) are proved.

## Completed moves

| Topic | Current owner | Result |
| --- | --- | --- |
| General event-measure limits | `MeasureTheory/Measure/SetLimits.lean` | Moved out of the probability application layer |
| Positive half-line mass | `MeasureTheory/Measure/PositiveTail.lean` | General measure statement; no probability-measure assumption added |
| Restricted nonnegative-integral limits | `MeasureTheory/Integral/Lebesgue/RestrictLimit.lean` | General result separated from the Poisson variation application |
| Truncation inequalities | `Order/Bounds/Truncation.lean` | Deterministic bounds separated from independent-event integration |
| Independent-event integration | `Probability/Independence/Integration.lean` | Independence-specific statements remain in probability |
| Feedback and one-jump bounds | `Order/Bounds/Feedback.lean`, `Order/Bounds/Corridor.lean` | Real/order arguments no longer live under Skorokhod geometry |
| Finite weighted-sum bounds | `Algebra/Order/BigOperators/WeightedSum.lean` | General sum inequalities separated from matrix spectral results |
| Declared-success stopping times | `Probability/Process/HittingTime/Declarations.lean` | General filtration statements use Mathlib stopping-time interfaces |
| Observable candidates and adapted recursion | `Probability/Process/HittingTime/ObservableCandidates.lean`, `Probability/Process/Adapted/Recursion.lean` | General process interfaces separated from branching applications |
| Reserve/restart estimates | `Probability/BranchingRandomWalk/Restart/` | Branching-specific hypotheses remain in the branching layer |
| Poisson window-integral vectors | `Probability/RandomMeasure/Poisson/WindowIntegral.lean` | Generic construction separated from stable-law identification |
| Cutoff Poisson path identities | `Probability/Process/Levy/Jump/PoissonConfiguration/Path.lean` | Reusable jump-configuration facts separated from stable-process laws |
| Convolution powers | `MeasureTheory/Measure/Convolution/Power.lean` | One recursive API remains; the old `convPow` module and definition were removed after proving the convolution-rotation relation |

The former source modules for M01--M10 and M13 have been removed. Mixed
application files for M03, M11, and M12 remain only for the results whose
statements still use those applications; they import the general module for
the lower-level facts. No compatibility aliases are retained for the removed
M13 convolution-power API.

## Verification

At the source revision for this status, the library target was verified with:

```sh
cd lean
lake build BranchingProcess
```

The move-specific source paths and theorem ownership were checked in the
modules listed above. Run the checks in [`CONTRIBUTING.md`](../../CONTRIBUTING.md)
after further API or import-boundary changes.

## Work outside this migration

Structural moves do not close the separate theorem gaps. Consult
[`FORMALIZATION_CHECKLIST.md`](../../FORMALIZATION_CHECKLIST.md) for the live
proof boundary, including stable-domain attraction, stable path tightness,
Mogulskii asymptotics, and the branching selection-speed statements. Any new
proof should first reuse the general measure, path, stopping-time, kernel, and
tree interfaces established above.

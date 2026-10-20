# Architecture migration status

This records the structural migration of general measure, deterministic,
stopping-time, Poisson, and branching interfaces. The status is checked
against the source tree at the repository revision carrying this document.
It does not claim that the separate open limit-theorem obligations in
[`FORMALIZATION_CHECKLIST.md`](../../FORMALIZATION_CHECKLIST.md) are proved.

## Completed moves

| Topic | Current owner | Result |
| --- | --- | --- |
| General event-measure limits | `MeasureTheory/Measure/Limits/SetLimits.lean` | Moved out of the probability application layer |
| Positive half-line mass | `MeasureTheory/Measure/Tails/Positive.lean` | General measure statement; no probability-measure assumption added |
| Restricted nonnegative-integral limits | `MeasureTheory/Integral/Lebesgue/RestrictLimit.lean` | General result separated from the Poisson variation application |
| Truncation inequalities | `Order/Bounds/Truncation.lean` | Deterministic bounds separated from independent-event integration |
| Independent-event integration | `Probability/Independence/Integration/Basic.lean` | Independence-specific statements remain in probability |
| Feedback and one-jump bounds | `Order/Bounds/Feedback.lean`, `Order/Bounds/Corridor.lean` | Real/order arguments no longer live under Skorokhod geometry |
| Finite weighted-sum bounds | `Algebra/Order/BigOperators/WeightedSum.lean` | General sum inequalities separated from matrix spectral results |
| Declared-success stopping times | `Probability/Process/HittingTime/Declarations.lean` | General filtration statements use Mathlib stopping-time interfaces |
| Observable candidates and adapted recursion | `Probability/Process/HittingTime/ObservableCandidates.lean`, `Probability/Process/Adapted/Recursion.lean` | General process interfaces separated from branching applications |
| Reserve/restart estimates | `Probability/BranchingRandomWalk/Restart/` | Branching-specific hypotheses remain in the branching layer |
| Poisson window-integral vectors | `Probability/RandomMeasure/Poisson/Integration/WindowIntegral.lean` | Generic construction separated from stable-law identification |
| Cutoff Poisson path identities | `Probability/Process/Levy/Jump/PoissonConfiguration/Path.lean` | Reusable jump-configuration facts separated from stable-process laws |
| Convolution powers | `MeasureTheory/Measure/Convolution/Power.lean` | One recursive API remains; the old `convPow` module and definition were removed after proving the convolution-rotation relation |
| Selection/NSelection boundary | `Probability/BranchingRandomWalk/Genealogy/RootIndexed/Field/Measurability.lean`, `Spine/Tube/`, `Selection/Finite/`, and `Selection/NSelection/{Speed,Tail}/` | Generic root-indexed position observations and path/tube estimates are separated from deterministic first-`N` speed and endpoint arguments; random finite-by-value constructors are under `Selection/Finite/` |
| Branching-walk structure | `Combinatorics/BranchingWalk/Basic/BranchingWalk.lean` | The root-indexed step-field and initial-position structure, its single-root specialization, and parent-closure interface have a semantic module name; declarations remain in `Combinatorics.Branching` because their mathematical ownership is unchanged |
| Paley--Zygmund inequality | `Probability/MeasureTheory/Moments/PaleyZygmund.lean` | The bound `(𝔼[X] - t)^2 / 𝔼[X^2] ≤ ℙ(t ≤ X)` now lives at its general probability-space level; Galton--Watson moment recurrences and endpoint-deviation rates remain in their owning modules |
| Positive-`a` first-stage proof chain | `Probability/BranchingRandomWalk/Selection/NSelection/EndpointDeviation/FirstStage/` | `LowCountPower.lean` is the first-stage conclusion; its one-use corridor budget and PZ assembly are grouped under `FirstStage/Lemmas/`. The folder name describes the proof stage, while the `rightTailPositiveA...` declarations retain the parameter regime. |
| Positive-`a` spine capacity estimate | `Probability/BranchingRandomWalk/Selection/NSelection/EndpointDeviation/Drawdown/Spine/` | `Capacity.lean` exposes the affine-corridor first-stage low-count estimate; `Window.lean` and `SecondStageTube.lean` own the restarted windows and second-stage path events; `FailureProbability.lean` is the entry for the endpoint-gap polynomial bound; six theorem-specific proof-chain modules remain under `Lemmas/`. The parameter condition remains in declaration names. |
| Infinite-offspring Kingman interface | `Probability/BranchingRandomWalk/Selection/NSelection/AsymptoticSpeed/Limit/InfiniteOffspring/` | Measurable batch repair, the subadditive array, Kingman limits, and leftmost speed have separate subject modules. `Kingman/Limit.lean` sits beside its proof chain in `Kingman/Lemmas/`; the unused reflection-based rightmost route was removed because `Rightmost.lean` obtains that result through `OrderDual`. |

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

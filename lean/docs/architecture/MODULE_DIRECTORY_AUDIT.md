# Dense Lean module directories

This audit uses direct `.lean` file counts, excluding `.lake` and test modules. A
large directory is split when several files form one proof chain or share a
specific mathematical subject. Independently reusable concepts remain in the
owning directory. For Lemma 3.5, `FiniteVarianceLower/EndpointBounds.lean` is
the entry point and `FiniteVarianceLower/Proof/Staircase/` holds its
one-purpose staircase chain. `FiniteVarianceLower/Binning/` and `Blocks/`
retain reusable real-width and conditional-block interfaces. This directory marks the module role; only Lean's `private` modifier
restricts a declaration to its defining module. A move preserves declaration
statements and proofs; a semantic move also updates the declaration namespace
and its import path.

## Reorganized proof families

| Family | Main entry or subject | Internal organization |
| --- | --- | --- |
| `RandomWalk/SmallDeviation/DriftedTube` | `FiniteVarianceLower/EndpointBounds.lean` contains both endpoint conclusions of Wang Yiyang's Lemma 3.5; `FiniteVarianceUpper.lean` states Lemma 3.4's upper estimate | `FiniteVarianceUpper/Blocks.lean` contains the conditional block construction for the upper estimate. `FiniteVarianceLower/Binning/Geometry.lean` owns the Lemma 3.5 spatial-bin construction. `Blocks` holds reusable conditional-block interfaces, while `Proof/Staircase` holds the lemma-specific assembly; the staircase has `Setup`, `Endpoint`, `Rate`, and `Concrete` steps. `Setup/FirstWindow.lean` and `Setup/EntranceBridge.lean` hold the first-block geometry and its entrance-event adapter. `EndpointEvent.lean`, `Reflection.lean`, and `BlockSchedule.lean` own the reusable endpoint events, symmetry, and finite block schedule. Within `Concrete`, `Lower.lean`, `Upper.lean`, and `Uniform.lean` are the internal assembly files; `Lower/` and `Upper/` group their respective entrance, global-condition, asymptotic, and conditional steps. |
| `RandomWalk/SmallDeviation/Drawdown` | `FiniteVarianceUpper.lean` states Wang Yiyang's Lemma 3.3 and its uniform and block-count forms | `FiniteVarianceUpper/ConditionalBlocks.lean` applies the general IID conditional-section bound from `Probability/Sequence/IID/ConditionalBlocks.lean` to drawdown events and proves the one-block estimates. `FiniteVarianceUpper/Proof.lean` contains the rounded-maximum, jump-pattern, and final rate arguments; its local product and sum bounds are reused inside the final theorem, so they remain private within that proof module. `Scaling.lean` states general event scaling identities and depends only on the drawdown event definition. |
| `RandomWalk/SmallDeviation/Range` | Independent bounded-range and block-oscillation small-deviation estimates | `GaussianCover.lean` gives the finite translated-corridor cover; `BlockOscillation.lean` gives the source-corridor comparison; `Rate.lean` derives the resulting Gaussian range rate. The unused old block-reindex adapter was removed. These estimates are separate from the Lemma 3.3 drawdown proof, which uses Lemma 3.2 directly. |
| `RandomWalk/SmallDeviation/HorizontalTube` | `FiniteVarianceUpper.lean` states Wang Yiyang's Lemma 3.2 and its translated-interval form | `FiniteVarianceUpper/Proof.lean` contains the equal-partition cover, fixed-corridor rate, block iteration, and remainder inputs. `FiniteVarianceLower.lean` owns the reusable endpoint-window consequence of Lemma 3.1(ii) and its uniform width/time threshold; Lemma 3.5 imports that estimate through `DriftedTube/FiniteVarianceLower/Binning`. |
| `RandomWalk/SmallDeviation/Entrance` | `FiniteVarianceEndpointCorridor.lean`, `RobustTransition.lean`, and `Robust/ExponentialBudget.lean` | Endpoint bridges and reusable edge geometry live in `FiniteVariance` and `Edge`. `Robust/Proof/` holds the three-region assembly for the fixed-window Appendix A.7 estimate, which remains private in `Robust/ExponentialBudget.lean`. The unused broad-window power-assembly branch in `Edge` was removed. `Rotation` groups the pathwise cyclic method used by `NormalDomain.lean`; generic finite-IID reindexing belongs to `Probability/Sequence/IID/FiniteReindex.lean`, and its measure-preserving finite-cover bound belongs to `MeasureTheory/Measure/FiniteCover.lean`. The normal-domain entrance bound is still imported by the selected-population second-stage bridge and spine estimates. Lemma 3.5's meander entrance uses the distinct finite-horizon i.i.d. cyclic-rotation inequality in `Fluctuation/SparreAndersen/RotationProbability.lean`; `FunctionalLimit/Conditioned/Transition/SurvivalLower.lean` combines it with the Gaussian endpoint-sign limit to obtain the inverse-square width bound. The uniform real-width threshold is proved in the Lemma 3.5 staircase module. |
| `RandomWalk/FunctionalLimit/Conditioned` | `FirstWindowLimit.lean` states Bolthausen's conditioned path limit; `MeanderIdentification.lean`, `MeanderVariance.lean`, and `DiffusiveTransitionLower.lean` state the downstream meander and transition results | `FirstWindow/FiniteTime.lean`, `FinitePathLimit.lean`, and `Absence.lean` hold finite-horizon and failure-event steps. `FirstWindow.lean` and `FirstWindowSelection.lean` stay at the outer level because their first-window law and selection interfaces can be imported independently. `Transition.lean` owns the finite transition event; `Transition/Factorization.lean`, `FromFirstWindow.lean`, `FromMeander.lean`, `DiffusiveFromMeander.lean`, and `SurvivalLower.lean` hold the independent product, conditioned-limit, and diffusive-survival steps. |
| `Selection/NSelection/EndpointDeviation` | Endpoint deviations of the selected population, including estimates that admit reflection | `Endpoint` contains moment and minimum lemmas; `Population`, `PositiveA`, and `SecondStage` contain the specialized right-tail proof chains. `SecondStage/Roots` and `SecondStage/Failure` identify their roles. The directory name does not impose a right-hand orientation. |
| `Selection/NSelection/AsymptoticSpeed` | Speed-limit statements and the selected-population speed proof | `InitialPopulation` holds its supporting coupling and measurability lemmas; `Environment` and `Selection` hold their respective supporting constructions. |
| `Mogulskii/RandomWalkBounds` and `Mogulskii/Stable/RandomWalkBounds` | Random-walk finite-block bounds and stable-domain random-walk rates | The former separates Donsker endpoint, source-partition, and partition arguments. `EndpointBands/Geometry.lean` owns the finite shifted-event construction, while `EndpointBands.lean` owns the killed-kernel iteration. The latter separates source, path-class, and partition arguments. The stable-process estimates remain in their own owner directory. `Mogulskii/Stable/Scale/Basic.lean` owns the two-scale condition and its rate consequences; the sibling `Scale.lean` owns block-length definitions and asymptotics. The diffusive endpoint CLT, finite Gaussian block-vector lower bound, and Gaussian product parameter choices are in `Mogulskii/Gaussian/BlockEndpoint.lean`, `BlockVector.lean`, and `ProductParameters.lean`; their namespace is `Mogulskii.Gaussian`. |
| `Stable/SmallDeviation/Blocks/Lower` | Lower block estimates | The feedback construction is grouped in `Feedback`; the other modules describe distinct lower-bound mechanisms. |
| `BranchingRandomWalk/Restart/RootedTrial` | Rooted-trial restart and coupling | Finite-slot and reserve arguments have their own subdirectories. |

## Dense directories retained at their current level

| Directory | Reason |
| --- | --- |
| `Combinatorics/BranchingWalk/Step`, `Combinatorics/BranchingWalk/Basic`, and `Combinatorics/BranchingWalk/Selection/NSelection` | Reusable step, genealogy, and selection interfaces are separated by theorem subject rather than one private proof chain. |
| `Probability/BranchingRandomWalk/Step` and `Probability/BranchingRandomWalk/Spine` | General branching-law and spine interfaces are called from multiple applications; their more specialized path and tube arguments already have subdirectories. |
| `Probability/RandomMeasure/Poisson` and `MeasureTheory/Measure` | Each file owns a separate measure or point-process operation, with no single main theorem for an additional inner layer. |
| `Probability/Process/RandomWalk/FunctionalLimit/Stable` | Centering, tightness, finite-dimensional convergence, and path limits are distinct reusable theorem interfaces. |
| `Probability/Process/RandomWalk/SmallDeviation/Mogulskii` and its `Spectral` subdirectory | The general rate and spectral interfaces already separate by mathematical input; narrower `Rate`, `Gaussian`, `Stable`, and spectral subdirectories are present. The fixed-parameter floor-grid argument now lives in `Rate/EndpointWindowSelection/FixedParameters.lean`; `Rate/EndpointWindowSelection.lean` selects the asymptotically sharp parameters and states the final rate. |
| `Topology/Cadlag/Skorokhod` and `Analysis/Asymptotics` | These files contain independent reusable topology and asymptotic lemmas. |

## A file and directory with the same name

Mathlib uses `Foo.lean` beside `Foo/` when the file is a useful entry point
or basic interface and the directory holds its component modules. This is a
module-path convention, not a duplicate Lean module. For example, the pinned
Mathlib source has `Tactic/Linarith.lean` beside `Tactic/Linarith/`. In this
library `InitialPopulation.lean`, `Endpoint.lean`, and
`Environment.lean` state substantive public results, so their sibling
folders hold supporting results. New files inside these folders use short
names such as `InitialPopulation/FreshField.lean` and
`Staircase/Endpoint/Margins.lean`. A same-name entry file should not be added
solely to re-export an entire directory; callers should import the narrow
owner module. The horizontal-tube lower bound formerly in
`DriftedTube/FiniteVarianceLower/Basic.lean` now lives in
`HorizontalTube/FiniteVarianceLower.lean`; the completed tilted-tube endpoint
theorem remains visible in `DriftedTube/FiniteVarianceLower/EndpointBounds.lean`.

`BranchingProcessTest` mirrors production module names where it has
corresponding tests. Its larger `Stable` and `Branching` directories are test
collections, not public theorem layers.

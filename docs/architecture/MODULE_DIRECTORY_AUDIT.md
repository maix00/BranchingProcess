# Dense Lean module directories

This audit uses direct `.lean` file counts, excluding `.lake` and test modules. A
large directory is split when several files form one proof chain or share a
specific mathematical subject. Independently reusable concepts remain in the
owning directory. The move changes import paths only; declaration namespaces,
statements, and proofs retain their existing names.

## Reorganized proof families

| Family | Main entry or subject | Internal organization |
| --- | --- | --- |
| `RandomWalk/SmallDeviation/DriftedTube` | `FiniteVarianceLower/EndpointBounds.lean` contains both endpoint conclusions of Wang Yiyang's Lemma 3.5; `FiniteVarianceUpper.lean` gives an upper estimate | `FiniteVarianceLower/Basic.lean` owns foundational horizontal-tube and bin interfaces. `Binning`, `Blocks`, and `Staircase` hold the lower-bound proof components; the staircase has `Setup`, `Endpoint`, `Rate`, and `Concrete` steps. |
| `RandomWalk/SmallDeviation/Entrance` | `FiniteVarianceEndpointCorridor.lean`, `RobustTransition.lean`, `RobustExponentialBudget.lean`, and `RobustUniformBudget.lean` | Endpoint bridges, edge arguments, and robust event arguments live in `FiniteVariance`, `Edge`, and `Robust`. `Rotation` groups the cyclic-path and exchangeability method used by `NormalDomain.lean`; the meander-based entrance used by Lemma 3.5 is reached through `RobustExponentialBudget.lean`. |
| `Selection/NSelection/EndpointDeviation` | Endpoint deviations of the selected population, including estimates that admit reflection | `Endpoint` contains moment and minimum lemmas; `Population`, `PositiveA`, and `SecondStage` contain the specialized right-tail proof chains. `SecondStage/Roots` and `SecondStage/Failure` identify their roles. The directory name does not impose a right-hand orientation. |
| `Selection/NSelection/AsymptoticSpeed` | Speed-limit statements and the selected-population speed proof | `InitialPopulation` holds its supporting coupling and measurability lemmas; `Environment` and `Selection` hold their respective supporting constructions. |
| `Mogulskii/RandomWalkBounds` and `Mogulskii/Stable/RandomWalkBounds` | Random-walk finite-block bounds and stable-domain random-walk rates | The former separates Donsker endpoint, source-partition, and partition arguments. The latter separates source, path-class, and partition arguments. The stable-process estimates remain in their own owner directory. |
| `Stable/SmallDeviation/Blocks/Lower` | Lower block estimates | The feedback construction is grouped in `Feedback`; the other modules describe distinct lower-bound mechanisms. |
| `BranchingRandomWalk/Restart/RootedTrial` | Rooted-trial restart and coupling | Finite-slot and reserve arguments have their own subdirectories. |

## Dense directories retained at their current level

| Directory | Reason |
| --- | --- |
| `Combinatorics/BranchingWalk/Step`, `Combinatorics/BranchingWalk/Basic`, and `Combinatorics/BranchingWalk/Selection/NSelection` | Reusable step, genealogy, and selection interfaces are separated by theorem subject rather than one private proof chain. |
| `Probability/BranchingRandomWalk/Step` and `Probability/BranchingRandomWalk/Spine` | General branching-law and spine interfaces are called from multiple applications; their more specialized path and tube arguments already have subdirectories. |
| `Probability/RandomMeasure/Poisson` and `MeasureTheory/Measure` | Each file owns a separate measure or point-process operation, with no single main theorem for an additional inner layer. |
| `Probability/Process/RandomWalk/FunctionalLimit/Stable` | Centering, tightness, finite-dimensional convergence, and path limits are distinct reusable theorem interfaces. |
| `Probability/Process/RandomWalk/SmallDeviation/Mogulskii` and its `Spectral` subdirectory | The general rate and spectral interfaces already separate by mathematical input; narrower `Rate`, `Gaussian`, `Stable`, and spectral subdirectories are present. |
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
owner module. The earlier `FiniteVarianceLower.lean` became
`FiniteVarianceLower/Basic.lean` once the completed endpoint theorem gained
its own visible entry point in `FiniteVarianceLower/EndpointBounds.lean`.

`BranchingProcessTest` mirrors production module names where it has
corresponding tests. Its larger `Stable` and `Branching` directories are test
collections, not public theorem layers.

# Dense Lean module directories

This audit uses direct `.lean` file counts, excluding `.lake` and test modules. A
large directory is split when several files form one proof chain or share a
specific mathematical subject. Independently reusable concepts remain in the
owning directory. For Lemma 3.5, `DriftedTube/FiniteVarianceLower/EndpointBounds.lean`
is the entry point and `DriftedTube/FiniteVarianceLower/Lemmas/Staircase/`
contains its one-purpose proof chain. Reusable real-width endpoint estimates,
block events, and moving-tube inclusions remain in `HorizontalTube/` and at
the `DriftedTube/` subject level. `Lemmas/` marks the module role; only Lean's
`private` modifier restricts a declaration to its defining module. A move
preserves theorem statements, proofs, and public declaration names unless an
API rename is explicitly needed. It changes import paths. A directory
grouping alone does not require a namespace rename; change the namespace when
mathematical ownership changes, and record deliberate namespace retention
when the move only clarifies module organization.

## Reorganized proof families

| Family | Main entry or subject | Internal organization |
| --- | --- | --- |
| `RandomWalk/SmallDeviation/DriftedTube` | `FiniteVarianceLower/EndpointBounds.lean` contains both endpoint conclusions of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5; `FiniteVarianceUpper/Basic.lean` formalizes Chapter 3, Lemma 3.4 | `Event.lean`, `FiniteVarianceUpper/Basic.lean`, and `FiniteVarianceUpper/Lemmas/Blocks.lean` use the matching namespace `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube`. `FiniteVarianceUpper/Lemmas/Blocks.lean` contains the theorem-specific conditional block proof. `FiniteVarianceLower/Lemmas/Staircase/Binning/` owns the Lemma 3.5 spatial-bin construction. `HorizontalTube/RealWidthLower.lean` owns reusable real-width endpoint-window bounds; `HorizontalTube/Blocks/` owns generic block events, conditional bounds, and product estimates. `BlockInclusion.lean` owns the reusable moving-tube inclusion. `FiniteVarianceLower/Lemmas/Staircase/` contains only the Lemma 3.5 assembly, divided into `Setup`, `Endpoint`, `Rate`, `Concrete`, and block steps. `FiniteVarianceLower/EndpointEvent.lean` and `FiniteVarianceLower/Reflection.lean` own the reusable endpoint event and its symmetry. `FiniteVarianceLower/Lemmas/Staircase/Setup/Schedule.lean` defines the finite staircase used only by the Lemma 3.5 proof, and `FiniteVarianceLower/Lemmas/Staircase/Rate/BlockExponential.lean` contains its exponential block-product identity. The entrance-rate allocation is in `FiniteVarianceLower/Lemmas/Staircase/Cost.lean`. The staircase-specific horizontal block intervals and widths are in `FiniteVarianceLower/Lemmas/Staircase/Setup/BlockTube.lean`. `FiniteVarianceLower/Lemmas/Staircase/Concrete/` contains the theorem-specific lower and upper bound assembly. |
| `RandomWalk/SmallDeviation/Drawdown` | `FiniteVarianceUpper/Basic.lean` formalizes Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.3 and its uniform consequence | `FiniteVarianceUpper/Lemmas/ConditionalBlocks.lean`, `Lemmas/JumpPattern/`, and `Lemmas/Rate/` hold the non-reusable conditional tube, rounded-maximum jump, union-bound, and rate steps. General conditional event iteration was moved to `Probability/Process/Filtration/ConditionalBlocks.lean`; translation of finite interval events moved beside its definition in `Path/Window/Basic.lean`, and IID finite-block interval-law transfer moved to `Path/Block/Law/FiniteInterval.lean`. The generic quotient estimate for a horizon divided by a floor-rounded block length is in `Analysis/Asymptotics/Scale/BlockScale.lean`. DriftedTube now uses `Fin.partialSum` and finite sums directly instead of importing Drawdown's finite-sum aliases. `Scaling.lean` remains outside the proof tree because its scaling identities apply to general event sets. |
| `RandomWalk/SmallDeviation/Range` | Independent bounded-range and block-oscillation small-deviation estimates | `GaussianCover.lean` gives the finite translated-corridor cover; `BlockOscillation.lean` gives the source-corridor comparison; `Rate.lean` derives the resulting Gaussian range rate. The unused old block-reindex adapter was removed. These estimates are separate from the Lemma 3.3 drawdown proof, which uses Lemma 3.2 directly. |
| `RandomWalk/SmallDeviation/HorizontalTube` | `FiniteVarianceUpper/Basic.lean` formalizes Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.2 and its translated-interval form | The module namespace is `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube`, including `FiniteVarianceUpper/Lemmas/`. `BlockIteration.lean` owns the reusable killed-interval kernel identity, uniform block estimate, and finite-horizon iteration. The theorem-specific equal-partition cover, fixed-corridor rate, and rate assembly are in `FiniteVarianceUpper/Lemmas/EqualPartition.lean` and `FiniteVarianceUpper/Lemmas/Rate.lean`. `EndpointWindow.lean` defines the translated and normalized endpoint-window events; `FiniteVarianceLower.lean` owns the reusable endpoint-window consequence of Chapter 3, Lemma 3.1(ii), and `RealWidthLower.lean` supplies uniform real-width thresholds. Lemma 3.5's staircase-specific bins live under `DriftedTube/FiniteVarianceLower/Lemmas/Staircase/Binning/`. |
| `RandomWalk/SmallDeviation/Entrance` | `FiniteVarianceEndpointCorridor.lean`, `RobustTransition.lean`, and `Robust/PowerAssembly.lean` | Endpoint bridges live in `FiniteVariance`; `Edge/PrefixSelection.lean` owns positive-mass fixed-prefix selection. The two wide moving-corridor inclusions formerly exposed under `Edge/` are now internal steps in `Robust/Lemmas/Edge/`; the actual narrowed terminal-window inclusions are in `Robust/Lemmas/EdgeGeometry.lean`, and the edge probability assembly is in `Robust/Lemmas/EdgeProbability.lean`. `Robust/PowerAssembly.lean` exposes the reusable power-bound assembly. The inverse-square estimate and polynomial-to-exponential bridge used only by Lemma 3.5 now live under `DriftedTube/FiniteVarianceLower/Lemmas/Staircase/Concrete/EntranceBudget.lean`, with the inverse-square estimates private in that file. The unused broad-window power-assembly branch in `Edge` was removed. `Rotation` groups the pathwise cyclic method used by `NormalDomain.lean`; generic finite-IID reindexing belongs to `Probability/Sequence/IID/FiniteReindex.lean`, and its measure-preserving finite-cover bound belongs to `MeasureTheory/Measure/Finite/Cover.lean`. The normal-domain entrance bound is still imported by the selected-population second-stage bridge and spine estimates. Lemma 3.5's meander entrance uses the distinct finite-horizon i.i.d. cyclic-rotation inequality in `Fluctuation/SparreAndersen/Rotation/Probability.lean`; `FunctionalLimit/Conditioned/Transition/SurvivalLower.lean` combines it with the Gaussian endpoint-sign limit to obtain the inverse-square width bound. The uniform real-width threshold is proved in the Lemma 3.5 staircase module. |
| `RandomWalk/FunctionalLimit/Conditioned` | Independent public interfaces by subject: `FirstWindow/`, `Meander/`, `Survival/`, and `Transition/` | `FirstWindow/Definition.lean` owns the prefix event and its measurability; `Selection.lean`, `Existence.lean`, `ConditionedLaw.lean`, `FiniteTime.lean`, `FinitePathLimit.lean`, `Absence.lean`, and `Limit.lean` remain direct complete constructions or limit results. The theorem-specific IID prefix/suffix factorization is grouped under `FirstWindow/Lemmas/BlockFactorization.lean`. The namespace remains `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned` because these declarations belong to the shared conditioned-random-walk interface; moving proof steps changes module organization, not mathematical ownership. `Meander/` contains the corridor probability, finite-variance limit, identification, and last-sign-change law. `Survival/` contains the conditioned law and scaling. `Transition/` contains the event and its factorization, meander limit, and diffusive lower bounds. |
| `Probability/Process/Path` and `Probability/Process/Brownian/AboveStart` | General path events and their Brownian specializations | `Path/FirstPassage/` groups first-passage, descending-hitting-time, reflection, and restart interfaces. `Path/AboveStart/FirstWindow/` groups path-level first-window results; `Brownian/AboveStart/FirstWindow/` contains the Brownian path-law and continuity results for the same construction. Random-walk path foundations are grouped into `Path/Adapted/` (filtration and martingale), `Path/Event/` (drawdown, survival, oscillation, and last sign change), and `Path/Representation/` (càdlàg paths, interpolation, and scaling); the `Basic`, `Window`, and `Skorokhod` entry modules remain at the root. |
| `Topology/Cadlag/Skorokhod` | Reusable topology and geometry for càdlàg paths with the Skorokhod metric | Public interfaces are grouped under `Compactness/`, `Corridor/`, `EDistance/`, `Evaluation/`, `Maps/`, `Oscillation/`, `Path/`, and `TimeChange/`. `Topology.lean` remains the subject-level topology interface; grouped modules are public mathematical results, not proof helpers. |
| `BranchingProcessTest` | Tests for the production library | Test modules are grouped by topic. Mogul'skii tests use `Mogulskii/{Axiom,Path,PathClass,Rates,Regression}/`; stable tests use `Attraction/`, `PathLaw/`, `RandomWalk/`, and `SmallDeviation/`; restart tests use `Branching/Restart/Trial/` and `Branching/Restart/Lineage/`; Skorokhod tests are grouped by topology operation. `scripts/run-all-lean-tests.py` and CI log paths follow these locations. |
| `Combinatorics/BranchingWalk/Basic` | Shared data and basic branching-walk operations | `Genealogy/` contains ancestor, descendant, and generation-size results; `Position/` contains displacement and position maps; `Sibling/` contains parent/sibling relations and closure properties; `Survival/` contains realized-particle and path-survival predicates; `Ordering/` contains orderability. `Definitions.lean` and `Map.lean` remain directly under `Basic/` as shared foundations. |
| `Combinatorics/BranchingWalk/Selection/NSelection` | Deterministic capacity-`N` selection and its induced walks | `Mechanism/` contains the selection rules, rank and value interfaces, and matching criteria; `Walk/` contains the bounded walk, its cloud, generation frontiers, and speed; `Coupling/` contains the coupling modules directly, with callers importing the specific result modules. `Basic.lean` remains the mechanism definition. |
| `Probability/BranchingRandomWalk/Spine` | Spine random walks, many-to-one identities, and tube moments | `ManyToOne/`, `RandomWalk/`, `PointMeasure/`, and `Tilted/` group the corresponding public constructions. `Path/` keeps its core interfaces at the root and groups decomposition, many-to-one, and second-moment results by subject. `Tube/` groups corridor, MRCA, and second-moment estimates. The declaration namespaces remain rooted at `ProbabilityTheory.BranchingRandomWalk.Spine` to preserve the existing API; only module paths changed. |
| `Probability/RandomMeasure/Poisson` | Poisson random measures and their public probability interfaces | `Integration/`, `Intensity/`, `JumpPath/`, and `Realization/` group integration identities, support and time-mark facts, path bounds, and finite-jump configurations. `Basic.lean`, `PointFamily.lean`, and `Superposition.lean` remain the direct core interfaces. The declarations retain the `ProbabilityTheory` namespace. |
| `Probability/Process/Brownian` | Brownian-process construction, continuous path laws, and support | `Construction/` groups existence and modification inputs; `PathLaw/` groups continuous versions and path-space laws; `Scaling/`, `Marginal/`, and `Support/` own the corresponding interfaces. `Reflection/` is divided into `Path/`, `FirstPassage/`, and `Descending/` families. |
| `Probability/Process/RandomWalk/FunctionalLimit/Stable` | Stable-domain path-law convergence and tightness | `PathLaw/` groups endpoint-grid identification, subsequential law construction, process-law construction, and convergence. `Tightness/` groups block tails, local oscillation, partition bounds, compact-range control, and the resulting tightness theorem. The finite-dimensional endpoint theorem and centering conditions remain at the subject root. |
| `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Spectral/Range` | Rademacher range small-deviation estimates from spectral interval bounds | `Blocks/` contains the one-block Donsker bounds; `Corridor/` contains the finite Brownian cover and killed-corridor comparison; `Rate/` contains parameter selection, logarithmic transfer, asymptotics, and the sharp upper rate. `Basic.lean` defines integer path coordinates, while `Probability.lean` retains the finite-time translated-interval cover. |
| `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Rate` | Public normal-domain small-deviation rate results | `Endpoint/` groups endpoint bands, windows, and parameter selection; `Partition/` groups finite covers and partitions; `Bounds/` groups interior, lower, upper, and variance estimates. The declarations keep their existing Mogulskii namespace because their mathematical ownership is unchanged. |
| `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Spectral` | Public spectral estimates for killed random walks | `Decomposition/` groups basis, modes, and expansion; `Kernel/` groups interval and killed transitions; `Survival/` groups path-survival bounds; `Rate/` groups asymptotics. `Basic.lean` remains the core interface, and all declarations retain the Mogulskii spectral namespace. |
| `Probability/Process/RandomWalk/Fluctuation/SparreAndersen` | Reusable finite IID fluctuation identities and survival estimates | `Rotation/` contains the cyclic cover and probability inequality; `Composition/` contains block factorization and the finite composition identity; `Survival/` contains the coefficient recurrence and finite-variance lower bound. These are general mathematical results and remain outside `Lemmas/`. |
| `Probability/Process/RandomWalk/Rademacher` | Results for the simple symmetric random walk | `Basic.lean`, `ConditionedPathLaw.lean`, and `LastSignChange.lean` are peer interfaces for the walk, its conditioned path law, and its last-sign-change index; `Terminal/` groups the terminal-path construction and convergence steps. |
| `BranchingRandomWalk/Selection/NSelection/AsymptoticSpeed/InitialPopulation` | Initial-population inputs to selected-walk speed estimates | `Basic.lean` is the entry interface; `Field/`, `Speed/`, and `Trajectory/` group the source field, speed estimates, and pathwise trajectory results. |
| `Selection/NSelection/EndpointDeviation` | Endpoint deviations of the selected population, including estimates that admit reflection | `Endpoint/` separates minimum, positive-moment, and sequence results. `Roots/`, `Drawdown/`, and `Rate/` group root estimates, population/spine drawdown bounds, and rate budgets. `Population/`, `PositiveA/`, and `SecondStage/` retain their theorem families; the directory name does not impose a right-hand orientation. |
| `Selection/NSelection/AsymptoticSpeed` | Speed-limit statements and the selected-population speed proof | `Limit/` groups the almost-sure product and subadditive limit results; `Selection/BlockComparison.lean` and `InitialPopulation/Speed/Basic.lean` state their respective public conclusions. `InitialPopulation/Basic.lean` is the entry module for the initial-population argument; `Field/`, `Trajectory/`, and `Speed/` group its field, hitting-time, and speed-transfer interfaces. `Environment/` and `Selection/` hold the remaining supporting constructions. |
| `Mogulskii/RandomWalkBounds` and `Mogulskii/Stable/RandomWalkBounds` | Random-walk finite-block bounds and stable-domain random-walk rates | The normal-domain root separates Donsker endpoint, endpoint-band geometry, horizontal tubes, and source-partition arguments. Stable random-walk bounds group `Bridge/`, `Endpoint/`, `Partition/`, `PathClass/`, and `Source/`; the stable-process estimates remain in their own owner directory. `Stable/RandomWalkBounds/FromIncrementLaw/` separates `Normal/`, `Path/`, and `Stable/` adapters, with `HorizontalTube/` holding the finite-variance tube interfaces. `Stable/Scale/Basic.lean` owns the two-scale condition and rate consequences; `Stable/Scale/Rate.lean` owns block-length asymptotics. Gaussian modules remain divided into `Gaussian/Blocks/` and `Gaussian/Path/`. `FunctionalLimit/Donsker/Entrance/` owns the Brownian middle-start corridor and uniform diffusive entrance estimates. |
| `Analysis/Asymptotics/Scale` | Reusable deterministic scale tools | `Basic.lean` defines the common small-deviation scale relation; `InverseScale.lean` handles generalized inverses and their subdiffusive rates; `BlockScale.lean`, `ShiftedFloor.lean`, and `IntermediatePowerBlock.lean` cover integer block rounding and intermediate block scales; `Sampling.lean` transfers rates along selected time intervals; `SlowDiagonal.lean` and `Tolerance.lean` provide real-valued diagonal and error-threshold selections. All eight direct modules are distinct reusable interfaces, so they remain as peers at this level. |
| `Stable/SmallDeviation/Blocks/Lower` | Lower block estimates | `Assembly/`, `Binning/`, `Bounds/`, `Entrance/`, and `Return/` group the distinct construction steps. The reusable feedback construction remains in `Feedback/`. |
| `BranchingRandomWalk/Restart/RootedTrial` | Rooted-trial restart and coupling | Finite-slot and reserve arguments have their own subdirectories. |
| `Combinatorics/BranchingWalk/Step` | Deterministic branching-step operations | The root keeps `Basic`, `Map`, `Measurability`, and `Relation`. Ordering properties and ranks are under `Ordering/`; slot selection and sibling closure are under `Selection/`; potential and point-measure operations are under `Measure/`; generation-local updates are under `Generation/`. |
| `Probability/BranchingRandomWalk/Step` | Random step presentations, fields, and laws | Coordinate presentations and their constructors/maps are under `Presentation/`; field operations under `Field/`; probability laws under `Law/`; measurable ordering under `Ordering/`; point-measure observations under `PointMeasure/`. Root-indexed position measurability remains under `Position/`. |

## Direct-module density and audited groupings

The inventory excludes `.lake` and vendored dependencies. More than eight
direct modules triggers a semantic grouping review; it does not by itself
justify a move into `Lemmas/`. Neither the production tree nor
`BranchingProcessTest` now has a directory with more than eight direct `.lean`
files. The dense families found in the initial inventory have now been grouped
by mathematical subject:

| Family | Public module organization |
| --- | --- |
| `MeasureTheory/Measure` | `Finite/`, `Algebra/`, `Limits/`, `Tails/`, `Windows/`, and `Levy/`; `Domination.lean` remains at the subject root. |
| `BranchingRandomWalk/Restart/RootedTrial` | `Completion/`, `Coupling/`, `Reward/`, and `Spine/`. |
| `BranchingRandomWalk/Population/Processes/StepSelection/SplitSchedule` | `Definition/`, `Field/`, and `Trials/`. |
| `Stable/SmallDeviation/PathClass/StepCorridor/Partition` | `Core/`, `Lower/`, and `Upper/`. |
| `Stable/SmallDeviation/Blocks/Lower` | `Assembly/`, `Binning/`, `Bounds/`, `Entrance/`, and `Return/`. |
| `RandomWalk/SmallDeviation/Mogulskii` | `Blocks/`, `Path/`, and `Scale/`; `Partition.lean` remains at the subject root. |
| `BranchingRandomWalk/Selection/NSelection/AsymptoticSpeed` | `Limit/` and `Selection/` group the main speed argument; `InitialPopulation/Basic.lean` remains the initial-population entry, with `Field/`, `Trajectory/`, and `Speed/` subfamilies. |
| `Mogulskii/Stable/RandomWalkBounds/FromIncrementLaw` | `Normal/`, `Path/`, and `Stable/`; `Normal/HorizontalTube/` groups the index-two finite-variance tube rate, endpoint-window forms, and their proof lemmas with the other normal-domain results. |
| `Mogulskii/Stable/RandomWalkBounds/FromIncrementLaw/Normal/HorizontalTube` | `Basic.lean` contains the core closed-tube rate, `Scales.lean` its scale specializations, and `EndpointWindow.lean` proves the endpoint-window rate using the event defined in the semantic `SmallDeviation/HorizontalTube/EndpointWindow.lean` module. The terminal-left source-corridor definitions and closed-tube comparisons used only by this proof are grouped in `Lemmas/SourceCorridor.lean`; the endpoint-window corridor union and source-path inclusion are in `Lemmas/EndpointWindowCorridor.lean`. The reusable unit-tube terminal-window construction is in `Topology/Cadlag/Skorokhod/PathClass/StepCorridor/TerminalWindow.lean`, and its all-exponent energy identity is in the corresponding `MeasureTheory/Measure/CadlagPath/PathClass/StepCorridor/TerminalWindow.lean`. |
| `Mogulskii/Stable/RandomWalkBounds/Source` | `Bounds/`, `Partition/`, and `PathClass/`; `Inputs.lean`, `Normalization.lean`, and `Realization.lean` remain at the source root. |
| `RandomWalk/Path/Interpolation` | `Finite/`, `Limit/`, and `Path/`; `Basic.lean` and `Scaling.lean` remain at the subject root. |
| `RandomWalk/FunctionalLimit/Donsker` | `FiniteDimensional/` and `Path/`; `FiniteDimensional.lean` is the subject entry module. |
| `Probability/Process/Path` | `Extrema/`, `Oscillation/`, `Reflection/`, `Representation/`, and `Scaling/`. |
| `Distributions/Stable/LevyMeasure` | `Cutoff/` and `Tail/`; scaling and jump-sign results remain at the subject root. |
| `Distributions/Stable` | `Domain/`, `Exponent/`, `Gaussian/`, `Levy/`, and `Operations/`; `Basic.lean` remains at the root. |
| `BranchingRandomWalk/Timing` | `Candidates/`, `Schedule/`, `Splits/`, and `Trials/`. |
| `BranchingRandomWalk/Restart` | `Failure/`, `Reserve/`, `Success/`, and `Trial/`; the `RootedTrial.lean` entry module and its component directory remain substantive. |
| `BranchingRandomWalk/Genealogy/RootIndexed` | `Field/` and `Law/`. |
| `Combinatorics/UlamHarris/Tree` | `Finite/` and `Topology/`; `Defs.lean` and `Singleton.lean` remain at the subject root. |
| `Selection/NSelection/EndpointDeviation/Endpoint` | `Minimum/`, `PositiveMoment/`, and `Sequence/`. |
| `Distributions/Stable/Attraction/Norming` | `Basic.lean`, `Inverse.lean`, `Compatibility.lean`, `Centering.lean`, `Source.lean`, `Tail.lean`, and `UniformTail.lean` remain at the subject root; Gaussian and index-two specializations are under `SpecialCases/`. |

## Same-stem files and directories

Mathlib permits a substantive `Foo.lean` interface beside `Foo/` when the
directory holds related component modules; for example, the pinned Mathlib
source has `Tactic/Linarith.lean` beside `Tactic/Linarith/`. This repository
uses a stricter local organization rule for discoverability: production and
test source trees contain no same-level `.lean` file and directory with the
same stem. The initial production-tree inventory had 81 such pairs; the test
tree had none. Their declarations now
live in `Foo/Basic.lean` or `Foo/Core.lean`, or in subject-specific children;
callers import those explicit modules. The moves preserve declaration names
and proofs while changing import paths. This rule does not prohibit a
substantive entry module where a future module family needs one; such a module
must expose a clear mathematical interface rather than only re-exporting the
directory. Four import-only facades were removed:
`NSelection/Coupling.lean`, `Processes/Concurrent.lean`,
`Processes/StepSelection.lean`, and `StepSelection/SplitSchedule.lean`.
Child filenames in the new `Spine/PointMeasure/`, `Spine/Tilted/`, and
branching-walk families use short subject-relative names instead of repeating
their parent directory. A repository-wide follow-up scan also normalized
`Analysis/Asymptotics/Power/PowerTailIntegral.lean` and
`Analysis/Asymptotics/Power/PowerSumLower.lean` to `TailIntegral.lean` and
`SumLower.lean`; `Probability/BranchingRandomWalk/Genealogy/Lineage/Lineages.lean`
to `PreSampled.lean`; `Probability/Distributions/Stable/LevyMeasure/Tail/Tails.lean`
to `Homogeneous.lean`; and
`Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Gaussian/Path/PathLawExistence.lean`
to `Existence.lean`, with sibling `PathClass.lean` renamed `ExplicitRate.lean`.
These are substantive mathematical modules; their declarations and namespaces
are unchanged, and callers import the new paths directly.

The final 2026-10-17 scan found 1,432 production modules and 138 test modules.
Across both trees there are zero same-stem file/directory collisions, zero
directories with more than eight direct Lean files, and zero child filenames
repeating their immediate parent directory name. The vendored Mathlib and
BrownianMotion trees are excluded from these project-layout counts. The
`InitialPopulation/` and `Rademacher/` groupings above were checked separately:
their remaining direct files are distinct entry interfaces, while their
larger proof families are grouped by mathematical role. The scan also caught
and fixed `Analysis/Asymptotics/Scale/Scale.lean`, now `Scale/Basic.lean`.

`BranchingProcessTest` mirrors production module names where it has
corresponding tests. Its larger `Stable` and `Branching` directories are test
collections, not public theorem layers. Test modules are grouped by the
mathematical API they exercise; this keeps test-only files out of production
`Lemmas/` trees while avoiding a large flat test directory.

## Citation audit

The production Lean source scan found no generic `the paper` or `the thesis`
citations, no LaTeX source labels, and no declaration names containing
`paper` or `thesis`. The citation review also corrected cases where the
English translation's title was presented as the Russian original, and
standardized the bibliographic details for Mogul'skii's article. The affected
comments now identify the relevant §1 definitions, Lemma 1(I) and its
equations (18)--(20), Lemma 2(a) equation (21), Lemma 2(c) equation (23), or
Theorem 3, Section 4 and equation (34), as appropriate. The repository rule
remains in [`CONTRIBUTING.md`](../../CONTRIBUTING.md): theorem docstrings name
the exact source result, and thesis references identify the exact title,
chapter, and displayed theorem or lemma number. Mogul'skii citations use the
Russian original's title and publication details from MathNet, together with
the English translation title and DOI; the translation volume and issue
follow SIAM's publisher record. The 2026-10-17 source-record check confirmed
the Russian article as volume 19, issue 4 (1974), and its English translation
as volume 19, issue 1 (1975). It corrected 119 English-translation citations
across 77 Lean and documentation files that had copied the Russian issue
number. The source-by-source check confirms
Aïdékon--Hu's Lemma 4.1 and Proposition 3.1, equations (4.15)--(4.16);
Caravenna--Chaumont's Lemma 2.1 and equations (2.3), (3.3); and the relevant
formulas of Bauer--Godrèche--Luck. Their locations are now distinguished
precisely: the cyclic event cover follows equation (A.3), the disjoint-block
factorization is (A.5)--(A.6), the generating-function derivation is
(A.7)--(A.8), and the finite coefficient recurrence is equation (2.2) in
Section 2. The Lean comments no longer cite (A.7) as the cyclic-cover
argument or as the finite recurrence.
The stable path-class regime modules now list their public declarations and
identify their shared logarithmic rate with Mogul'skii's Theorem 3, Section 4,
p. 764; the source-normalized and finite-partition versions give the same
specific citation. Thesis-based scale, Potter-bound, and corridor modules
name Wang Yiyang's full thesis title, institution and year, and the exact
chapter or Appendix A.2 lemma they use.

The audit also added full module-level declaration lists and mathematics to
the endpoint-constrained comparison, range comparison, stable path-class rate,
endpoint-band lower-rate, and normal-domain return-block modules. Their theorem
docstrings now identify Mogul'skii's exact Lemma 2(a), relation (21), Lemma
2(b), equation (23), or Theorem 3, Section 4, p. 764, as applicable. The
finite-variance endpoint-window route also names Wang Yiyang's thesis and
Chapter 3, Lemma 3.1(i); the generic Gaussian return-block bounds list their
quantitative interfaces without attributing an internal estimate to an
external lemma.

The corresponding works are Elie Aïdékon and Yueyun Hu, *Average-weight
percolation on the complete graph*, Lemma 4.1 and Proposition 3.1; Francesco
Caravenna and Loïc Chaumont, *Invariance principles for random walks
conditioned to stay positive*, Lemma 2.1; and M. Bauer, C. Godrèche, and
J.-M. Luck, *Statistics of persistent events in the binomial random walk: Will
the drunken sailor hit the sober man?*, Section 2 and Appendix A. Wang Yiyang's
thesis citations name *Asymptotic Speed of the N-Branching Random Walk with
Infinite Offspring*, Chapter 3 and the displayed lemma number, or Appendix A.2,
Lemma A.7.

The Iglehart citations for the Brownian last-zero realization now locate
Section 3, theorem (3.4), p. 616, and the paragraph that gives its
last-zero representation. This is the displayed number `(3.4)` on p. 616,
not a claim that the article labels it "Theorem 3.4". The primary records are
[Aïdékon--Hu](https://arxiv.org/abs/2512.23266),
[Caravenna--Chaumont](https://doi.org/10.1214/07-AIHP119),
[Bauer--Godrèche--Luck](https://doi.org/10.1023/A:1004636216365),
[Bolthausen](https://doi.org/10.1214/aop/1176996098),
[Iglehart](https://doi.org/10.1214/aop/1176996607),
[Dilworth--Wright](https://arxiv.org/abs/1810.01783),
[MathNet's record of Mogul'skii's Russian original](https://www.mathnet.ru/eng/tvp3978),
and [SIAM's record of its English translation](https://epubs.siam.org/doi/10.1137/1119081).
The Brownian reflection and conditioned-walk comments also identify Dilworth--Wright's
Theorem 2.1; Bolthausen's Lemma 2.2, Lemma 2.3 equation (2.2), and Theorem
3.2; and Iglehart's displayed equation (3.4), Section 3, p. 616. Wang Yiyang's
thesis references give its full title and the exact chapter and lemma number.

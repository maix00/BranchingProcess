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
| `RandomWalk/SmallDeviation/DriftedTube` | `FiniteVarianceLower/EndpointBounds.lean` contains both endpoint conclusions of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5; `FiniteVarianceUpper/Basic.lean` formalizes Chapter 3, Lemma 3.4 | `Event.lean` owns the full tilted-tube event; `BlockEvent.lean` owns the reusable pair and full-sequence events for one finite block. `FiniteVarianceUpper/Lemmas/Blocks.lean` contains the theorem-specific conditional block proof. The bin endpoints, narrowed width, and terminal fractions are internal parameters in `FiniteVarianceLower/Lemmas/Staircase/Setup/Binning.lean`; the ordinary and terminal block windows and horizontal sub-tube geometry are grouped in `Setup/EndpointWindow.lean` and `Setup/BlockTube.lean`. The finite-cover proof and parameter selection are in `FiniteVarianceLower/Lemmas/Staircase/Binning/`. `HorizontalTube/RealWidthLower.lean` owns reusable real-width endpoint-window bounds; `HorizontalTube/Blocks/` owns generic block events, conditional bounds, and product estimates. `BlockInclusion.lean` owns the reusable moving-tube inclusion. `FiniteVarianceLower/Lemmas/Staircase/` contains the Lemma 3.5 proof assembly, divided into `Setup`, `Endpoint`, `Rate`, `Concrete`, and block steps. `FiniteVarianceLower/EndpointEvent.lean` and `FiniteVarianceLower/Reflection.lean` own the reusable endpoint event and its symmetry. The generic quotient/remainder schedule and its natural-number count, endpoint, and block-length facts are all in `Path/Block/Partition/TailMerged.lean`; the separate `Analysis/Asymptotics/Scale/BlockScale.lean` balanced partition distributes remainders instead of absorbing them into the last block. The Lemma 3.5-specific tube-width and endpoint margins stay under `FiniteVarianceLower/Lemmas/Staircase/Setup/`, while the schedule's exponential product identity is in `FiniteVarianceLower/Lemmas/Staircase/Rate/BlockExponential.lean`. The entrance-rate allocation is in `FiniteVarianceLower/Lemmas/Staircase/Cost.lean`. `FiniteVarianceLower/Lemmas/Staircase/Concrete/` contains the theorem-specific lower and upper bound assembly. |
| `RandomWalk/SmallDeviation/Drawdown` | `FiniteVarianceUpper/Basic.lean` formalizes Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.3 and its uniform consequence | `Path/Event/Drawdown.lean` owns the reusable finite-history drawdown predicates and their measurability. `FiniteVarianceUpper/TubeEvent.lean` owns the finite-pair and sequence-level horizontal drawdown tube events, which are the reusable semantic interface. The finite-prefix path, running-maximum spatial bins, jump-pattern events, factors, and admissible pattern family are specific to Lemma 3.3 and live under `FiniteVarianceUpper/Lemmas/JumpPattern/`. `FiniteVarianceUpper/Lemmas/ConditionalBlocks.lean`, `Lemmas/JumpPattern/`, and `Lemmas/Rate/` contain the non-reusable conditional tube, rounded-maximum jump, union-bound, and rate proofs. General conditional event iteration was moved to `Probability/Process/Filtration/ConditionalBlocks.lean`; translation of finite interval events moved beside its definition in `Path/Window/Basic.lean`, and IID finite-block interval-law transfer moved to `Path/Block/Law/FiniteInterval.lean`. The generic quotient estimate for a horizon divided by a floor-rounded block length is in `Analysis/Asymptotics/Scale/BlockScale.lean`. DriftedTube now uses `Fin.partialSum` and finite sums directly instead of importing Drawdown's finite-sum aliases. `Scaling.lean` remains outside the proof tree because its scaling identities apply to general event sets. |
| `RandomWalk/SmallDeviation/Range` | Independent bounded-range and block-oscillation small-deviation estimates | `GaussianCover.lean` gives the finite translated-corridor cover; `BlockOscillation.lean` gives the source-corridor comparison; `Rate.lean` derives the resulting Gaussian range rate. The unused old block-reindex adapter was removed. These estimates are separate from the Lemma 3.3 drawdown proof, which uses Lemma 3.2 directly. |
| `RandomWalk/Fluctuation` | Random-walk records, ladder variables, and Sparre--Andersen identities | `Ladder/RecordLocalTime.lean` and `Ladder/Ascending.lean` define ascending records, local time, ladder times, and heights. `Ladder/Descending/` groups the reflected record/local-time interface, the descending renewal function, the finite-variance ladder-time finiteness result, and the stable-attraction tail theorem. `FiniteVarianceSignLimit.lean` remains at the subject root as the general Gaussian positivity-parameter and Spitzer-condition input. `SparreAndersen/Rotation/` contains the public cyclic-rotation cover and IID probability inequality; `Composition/Cyclic.lean` and `Composition/CyclicReindex.lean` expose the reusable gap-composition equivalence and arbitrary-weight sum reindexing, while the event-decomposition and block-probability proof chain is isolated in `Composition/Lemmas/`; `Survival/` contains the finite-variance lower bounds and recurrence interface. The declarations retain the `ProbabilityTheory.RandomWalk` namespace because each interface is stated for increment paths; the directory move groups the ladder-variable subject without changing ownership. The source citations identify Chaumont--Doney's equation (2.2) and Lemma 5, Caravenna--Chaumont's Lemma 2.1 and equation (2.3), and Doney's Theorem 2. |
| `Probability/BranchingRandomWalk/Population/Processes/Causal` | Causal genealogical populations and their capacity/path interfaces | The root keeps `Basic.lean`, `Predicate.lean`, and `Genealogy.lean` as the population construction, predicate selection, and samplewise genealogy interfaces. `Path/{Window,Bound}.lean` groups finite-history path representations and the reusable pathwise population bound. `Capacity/{Basic,FirstMoment,Spine}.lean` groups generic Markov capacity estimates and their first-moment/spine consequences. These are complete results for the causal-population interface, not fragments of one theorem-specific proof; `RelativePosition/` remains its own reusable path-position family. |
| `Probability/Process/RandomWalk/Kernel/Killed` | Reusable kernel interfaces for random walks killed on exit | `Basic.lean` defines the restricted transition kernel; `Comparison.lean` compares its survival mass; `Partition.lean` identifies equal-block survival with the path event. `Return/` groups endpoint distributions, target entrance, and terminal bridges; `Survival/` groups block iteration and uniform bounds. These are complete kernel statements reused by multiple small-deviation arguments, so they remain outside `Lemmas/`. |
| `Probability/Sequence/IID` | Canonical laws and reusable interfaces for independent identically distributed sequences | `Basic.lean`, `Law.lean`, `Filtration.lean`, `CharacteristicFunction.lean`, and `FiniteReindex.lean` remain direct peers for the canonical product law, law identification, prefix-filtration independence, characteristic functions, and finite coordinate symmetry. `Blocks/` groups the complete stopping-time, deterministic-prefix, and conditional block APIs; these are reusable mathematical results and therefore remain outside `Lemmas/`. |
| `Probability/ConvergenceInDistribution` | Core weak-convergence interfaces | `Basic.lean`, `Portmanteau.lean`, `Mapping.lean`, `Independence.lean`, `DeterministicParameter.lean`, and `EscapingMixture.lean` remain direct peer interfaces: they define convergence compatibility, event bounds, continuous mappings, independent products, deterministic-coordinate products, and escaping finite mixtures. The related approximation principles are grouped under `Approximation/{AsymptoticEquivalence,Finite}.lean`; both are complete reusable results, so this semantic grouping does not use `Lemmas/`. The three core modules now list all public declarations and state their formulas and assumptions in the module headers.
| `RandomWalk/SmallDeviation/Mogulskii/RandomWalkBounds/Partition` | Floor-rounded finite-partition bounds for normalized step corridors | `Corridor.lean` gives the grid-cell lengths and the upper range-probability product; `Range.lean` owns the IID block-oscillation and product estimates; `Endpoint.lean` owns the endpoint-core block event, its IID factorization, and knot induction; `LowerProbability.lean` assembles these into the corridor lower bound. `Lemmas/LowerGeometry.lean` contains only the theorem-specific deterministic gluing step from local block events to the global corridor event. It retains the `Discrete` namespace because the namespace describes the mathematical interface, while the move only groups the proof module. The lower-probability entry imports this helper ordinarily; its presence under `Lemmas/` indicates proof-chain role, while Lean declaration visibility is governed separately by `private` and the module import. |
| `RandomWalk/SmallDeviation/Mogulskii/Stable/Rate` | Exact centered horizontal-tube rate under a stable escape-rate hypothesis | `Upper.lean` gives the upper rate; `Lower/BlockProbability.lean` gives the endpoint-return block estimate; `Lower/Liminf.lean` derives strict-subtube and optimized lower rates; `Lower/Positivity.lean` supplies the real-log conditions used by the upper proof; `Lower/Limit.lean` identifies the limit. These complete mathematical interfaces remain outside `Lemmas/`. The partition probability module imports only `Lower/Positivity`, while the final rate test imports `Lower/Limit`. |
| `RandomWalk/SmallDeviation/Mogulskii/RandomWalkBounds/SourcePartition` | Matching partition estimates for the source terminal-left convention | `Basic.lean` records the clipped terminal knot index and source cell lengths; `Events.lean` gives the selected-cell range upper bound; `LowerProbability.lean` is the lower-bound entry. `Lemmas/LowerGeometry.lean` contains the source-specific deterministic gluing step and is imported ordinarily by the entry. The public interfaces remain beside the `Lemmas/` directory, and the `Discrete` namespace remains unchanged. |
| `RandomWalk/SmallDeviation/HorizontalTube` | `FiniteVarianceUpper/Basic.lean` formalizes Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.2 and its translated-interval form | The module namespace is `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube`, including `FiniteVarianceUpper/Lemmas/`. `BlockIteration.lean` owns the reusable killed-interval kernel identity, uniform block estimate, and finite-horizon iteration. The equal-partition and block-length parameters specific to Lemma 3.2, along with its cover, fixed-corridor rate, and rate assembly, are grouped under `FiniteVarianceUpper/Lemmas/Partition/`, `Lemmas/EqualPartition.lean`, and `Lemmas/Rate.lean`. `EndpointWindow.lean` defines the translated and normalized endpoint-window events; `FiniteVarianceLower.lean` owns the reusable endpoint-window consequence of Chapter 3, Lemma 3.1(ii), and `RealWidthLower.lean` supplies uniform real-width thresholds. Lemma 3.5's staircase-specific bins and endpoint fractions live under `DriftedTube/FiniteVarianceLower/Lemmas/Staircase/Setup/`; the finite-cover proof and selection lemmas are under `Lemmas/Staircase/Binning/`. |
| `RandomWalk/SmallDeviation/Entrance` | `FiniteVarianceEndpointCorridor.lean` and public interfaces with applications to multiple small-deviation arguments | `MovingCorridor.lean` owns the reusable moving-boundary path event and its constant-corridor inclusion, with no terminal-window parameter. `Edge/PrefixSelection.lean` retains the reusable positive-mass increment-window construction; its width inequalities specific to the Lemma 3.5 edge argument are in `Robust/Lemmas/Edge/PrefixGeometry.lean`. `Robust/Event.lean` defines the fixed `[2Δ/5,3Δ/5]` entrance event used in Chapter 3, Lemma 3.5; `Robust/Measurability.lean` proves its prefix-filtration measurability. The inclusion of the Donsker interior event in this narrower-window event is a theorem-specific step in `Robust/Lemmas/Event.lean`. The theorem-specific middle-start estimate, edge products, three-region minimum, and event inclusions remain under `Robust/Lemmas/`. The exponent-uniform assembly from forward and reflected transition-power bounds to a uniform robust-event lower bound is the reusable interface `Robust/PowerLower.lean`; it accepts every positive exponent and is used by the Appendix A.2, Lemma A.7 entrance estimate in the proof of Chapter 3, Lemma 3.5. The inverse-square estimate and polynomial-to-exponential bridge used only by Lemma 3.5 live under `DriftedTube/FiniteVarianceLower/Lemmas/Staircase/Concrete/EntranceBudget.lean`, with the inverse-square estimates private in that file. The unused broad-window power-assembly branch in `Edge` was removed. `Rotation/FinitePath.lean` defines the finite increment path and measurable corridor events; `Rotation/CyclicCover.lean` proves the deterministic path-ball cover by cyclic reindexing; `Rotation/FiniteProduct.lean` converts it to the finite-IID probability bound used by `NormalDomain.lean`. Generic finite-IID reindexing belongs to `Probability/Sequence/IID/FiniteReindex.lean`, and its measure-preserving finite-cover bound belongs to `MeasureTheory/Measure/Finite/Cover.lean`. The normal-domain entrance bound is still imported by the selected-population second-stage bridge and spine estimates. Lemma 3.5's meander entrance uses the distinct finite-horizon i.i.d. cyclic-rotation inequality in `Fluctuation/SparreAndersen/Rotation/Probability.lean`; `FunctionalLimit/Conditioned/Transition/SurvivalLower.lean` combines it with the Gaussian endpoint-sign limit to obtain the inverse-square width bound. The uniform real-width threshold is proved in the Lemma 3.5 staircase module. |
| `RandomWalk/FunctionalLimit/Conditioned` | Independent public interfaces by subject: `FirstWindow/`, `Meander/`, `Survival/`, and `Transition/` | `FirstWindow/Definition.lean` owns the prefix event and its measurability; `Selection.lean`, `Existence.lean`, `ConditionedLaw.lean`, `FiniteTime.lean`, `FinitePathLimit.lean`, `Absence.lean`, and `Limit.lean` remain direct complete constructions or limit results. The theorem-specific IID prefix/suffix factorization is grouped under `FirstWindow/Lemmas/BlockFactorization.lean`. The namespace remains `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned` because these declarations belong to the shared conditioned-random-walk interface; moving proof steps changes module organization, not mathematical ownership. `Meander/CorridorProbability.lean` contains the public open-corridor Portmanteau lower bound. `Survival/` contains the conditioned law and scaling. `Transition/Event.lean` owns the finite transition event, its normalized path corridor, equivalences, factorization, and diffusive horizon. The convergence-to-corridor and corridor-to-conditional-probability steps used in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5 are grouped under `Transition/Lemmas/CorridorProbability.lean`; `Transition/` contains the remaining meander limit and diffusive lower bounds. |
| `Probability/Process/Path` and `Probability/Process/Brownian/AboveStart` | General path events and their Brownian specializations | `Path/FirstPassage/` groups first-passage, descending-hitting-time, reflection, and restart interfaces. `Path/AboveStart/FirstWindow/` groups path-level first-window results; `Brownian/AboveStart/FirstWindow/` keeps the finiteness and first-window-time continuity entries at its root; `Shift/` groups the uncentered, centered, finite-horizon, and cutoff-limit path-shift continuity results, which form one coherent path-transform family. Random-walk path foundations are grouped into `Path/Adapted/` (filtration and martingale), `Path/Event/` (drawdown, survival, oscillation, and last sign change), and `Path/Representation/` (càdlàg paths, interpolation, and scaling); the `Basic`, `Window`, and `Skorokhod` entry modules remain at the root. |
| `Topology/Cadlag/Skorokhod` | Reusable topology and geometry for càdlàg paths with the Skorokhod metric | Public interfaces are grouped under `Compactness/`, `Corridor/`, `EDistance/`, `Evaluation/`, `Maps/`, `Oscillation/`, `Path/`, and `TimeChange/`. `Topology.lean` remains the subject-level topology interface. `TimeChange/Limit/` groups the summable-distortion convergence chain; `EDistance/Logarithmic/Completion/` groups the aligned Cauchy construction, subsequence extraction, limit identification, and completeness theorem. These are complete reusable convergence results, so they are grouped by mathematical role rather than under `Lemmas/`. |
| `BranchingProcessTest` | Tests for the production library | Test modules are grouped by topic. Mogul'skii tests use `Mogulskii/{Axiom,Path,PathClass,Rates,Regression}/`; stable tests use `Attraction/`, `PathLaw/`, `RandomWalk/`, and `SmallDeviation/`; restart tests use `Branching/Restart/Trial/` and `Branching/Restart/Lineage/`; Skorokhod tests are grouped by topology operation. `scripts/run-all-lean-tests.py` and CI log paths follow these locations. |
| `Combinatorics/BranchingWalk/Basic` | Shared data and basic branching-walk operations | `Genealogy/` contains ancestor, descendant, and generation-size results; `Position/` contains displacement and position maps; `Sibling/` contains parent/sibling relations and closure properties; `Survival/` contains realized-particle and path-survival predicates; `Ordering/` contains orderability. `Definitions.lean` and `Map.lean` remain directly under `Basic/` as shared foundations. |
| `Combinatorics/BranchingWalk/Selection/NSelection` | Deterministic capacity-`N` selection and its induced walks | `Mechanism/` contains the selection rules, rank and value interfaces, and matching criteria; `Walk/` contains the bounded walk, its cloud, generation frontiers, and speed; `Coupling/` contains the coupling modules directly, with callers importing the specific result modules. `Basic.lean` remains the mechanism definition. |
| `Probability/BranchingRandomWalk/Spine` | Spine random walks, many-to-one identities, and tube moments | `ManyToOne/`, `RandomWalk/`, `PointMeasure/`, and `Tilted/` group the corresponding public constructions. `Path/` keeps its core interfaces at the root and groups decomposition, many-to-one, and second-moment results by subject. `Tube/` groups corridor, MRCA, and second-moment estimates. The declaration namespaces remain rooted at `ProbabilityTheory.BranchingRandomWalk.Spine` to preserve the existing API; only module paths changed. |
| `Probability/RandomMeasure/Poisson` | Poisson random measures and their public probability interfaces | `Integration/`, `Intensity/`, `JumpPath/`, and `Realization/` group integration identities, support and time-mark facts, path bounds, and finite-jump configurations. `Basic.lean`, `PointFamily.lean`, and `Superposition.lean` remain the direct core interfaces. The declarations retain the `ProbabilityTheory` namespace. |
| `Probability/Process/Brownian` | Brownian-process construction, continuous path laws, and support | `Construction/` groups existence and modification inputs; `PathLaw/` groups continuous versions and path-space laws; `Scaling/`, `Marginal/`, and `Support/` own the corresponding interfaces. `Reflection/` is divided into `Path/`, `FirstPassage/`, and `Descending/` families. |
| `Probability/Process/Path/Skorokhod/Corridor/UniformBlocks` | Finite uniform partitions of path corridors | `Feedback/Basic.lean` defines the sign-selected block and prefix events and their pathwise identities; `Feedback/FullPath.lean` gives the reusable càdlàg transfer from rational-coordinate bounds to a full-path tube. Both are mathematical interfaces, so they remain outside `Lemmas/`. |
| `Probability/Process/RandomWalk/FunctionalLimit/Stable` | Stable-domain path-law convergence and tightness | `PathLaw/` groups endpoint-grid identification, subsequential law construction, process-law construction, and convergence. `Tightness/` groups block tails, local oscillation, partition bounds, compact-range control, and the resulting tightness theorem. The finite-dimensional endpoint theorem and centering conditions remain at the subject root. |
| `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Spectral/Range` | Rademacher range small-deviation estimates from spectral interval bounds | `Blocks/` contains the one-block Donsker bounds; `Corridor/` contains the finite Brownian cover and killed-corridor comparison; `Rate/` contains parameter selection, logarithmic transfer, asymptotics, and the sharp upper rate. `Basic.lean` defines integer path coordinates, while `Probability.lean` retains the finite-time translated-interval cover. |
| `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Rate` | Public normal-domain small-deviation rate results | `Endpoint/` groups endpoint bands, windows, and parameter selection; `Endpoint/Selection/Basic.lean` is the public sharp-rate conclusion, while its floor choices and fixed-parameter proof step are in `Endpoint/Selection/Lemmas/FixedParameters.lean`. `Partition/` groups finite covers and partitions; `Bounds/` groups interior, lower, upper, and variance estimates. The declarations keep their existing Mogulskii namespace because their mathematical ownership is unchanged. |
| `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Spectral` | Spectral estimates for the killed symmetric walk, including diffusive Brownian corridor and endpoint-window bounds | `Kernel/` defines the finite killed transition; `Decomposition/` gives its sine basis, modes, and target-set expansion; `Target/` owns parity-compatible central targets, their principal-mode mass bounds, and the path-event interpretation. These target estimates are parameterized by the target set, interval width, and block scale, so they remain reusable interfaces. `Survival/` groups path-survival bounds; `Scaling/` and `Rate/` contain the diffusive logarithmic limits and analytic asymptotics; `Diffusive/` transfers the spectral lower bound through Donsker convergence to Brownian corridors and return kernels. The finite-cover range upper bound remains in the separate `Range/` family. `Basic.lean` is the core interface, and declarations retain the Mogulskii spectral namespace. |
| `Probability/Process/RandomWalk/Fluctuation/SparreAndersen` | Reusable finite IID fluctuation identities and survival estimates | `Rotation/` contains the cyclic cover and probability inequality; `Composition/` contains block factorization and the finite composition identity; `Survival/` contains the coefficient recurrence and finite-variance lower bound. These are general mathematical results and remain outside `Lemmas/`. |
| `Probability/Process/RandomWalk/Rademacher` | Results for the simple symmetric random walk | `Basic.lean`, `ConditionedPathLaw.lean`, and `LastSignChange.lean` are peer interfaces for the walk, its conditioned path law, and its last-sign-change index; `Terminal/` groups the terminal-path construction and convergence steps. |
| `BranchingRandomWalk/Selection/NSelection/AsymptoticSpeed/InitialPopulation` | Initial-population inputs to selected-walk speed estimates | `Basic.lean` is the exact-$N$ split-event and speed-transport interface; `Field/` and `Speed/` group the source field and speed estimates. In `Trajectory/`, `Population.lean` owns the selected-population construction, `Hitting.lean` is the capacity-hitting entry theorem, and `Lemmas/CapacityHit/{Mark,Growth}.lean` contains its proof-specific mark and cardinality-growth chain. |
| `Selection/NSelection/EndpointDeviation` | Endpoint deviations of the selected population, including estimates that admit reflection | `Endpoint/` separates minimum, positive-moment, and sequence results. `Roots/`, `Drawdown/`, and `Rate/` group root estimates, population/spine drawdown bounds, and rate budgets. `Population/`, `PositiveA/`, and `SecondStage/` retain their theorem families; the directory name does not impose a right-hand orientation. |
| `Selection/NSelection/AsymptoticSpeed` | Speed-limit statements and the selected-population speed proof | `Limit/` groups the almost-sure product and subadditive limit results; `Selection/BlockComparison.lean` and `InitialPopulation/Speed/Basic.lean` state their respective public conclusions. `InitialPopulation/Basic.lean` is the entry module for the initial-population argument; `Field/`, `Trajectory/`, and `Speed/` group its field, hitting-time, and speed-transfer interfaces. `Environment/` and `Selection/` hold the remaining supporting constructions. |
| `Mogulskii/RandomWalkBounds` and `Mogulskii/Stable/RandomWalkBounds` | Random-walk finite-block bounds and stable-domain random-walk rates | The normal-domain root separates Donsker endpoint, endpoint-band geometry, horizontal tubes, and source-partition arguments. Stable random-walk bounds group `Bridge/`, `Endpoint/`, `Partition/`, `PathClass/`, and `Source/`; the stable-process estimates remain in their own owner directory. `Stable/RandomWalkBounds/FromIncrementLaw/` separates `Normal/`, `Path/`, and `Stable/` adapters, with `HorizontalTube/` holding the finite-variance tube interfaces. `Stable/Scale/Basic.lean` owns the two-scale condition and rate consequences; `Stable/Scale/Rate.lean` owns block-length asymptotics. Gaussian modules remain divided into `Gaussian/Blocks/` and `Gaussian/Path/`. `FunctionalLimit/Donsker/Entrance/` owns the Brownian middle-start corridor and uniform diffusive entrance estimates. |
| `Analysis/Asymptotics/Scale` | Reusable deterministic scale tools | `Basic.lean` defines the common small-deviation scale relation; `InverseScale.lean` handles generalized inverses and their subdiffusive rates; `BlockScale.lean`, `ShiftedFloor.lean`, and `IntermediatePowerBlock.lean` cover integer block rounding and intermediate block scales; `Sampling.lean` transfers rates along selected time intervals; `SlowDiagonal.lean` and `Tolerance.lean` provide real-valued diagonal and error-threshold selections. All eight direct modules are distinct reusable interfaces, so they remain as peers at this level. |
| `Analysis/Asymptotics/RegularVariation` | Regular variation, slow variation, and Karamata-type consequences | `Basic.lean`, `Uniform.lean`, `AsymptoticInverse.lean`, `LowerPower.lean`, `MonotoneDensity.lean`, and `SlowScale.lean` remain at the subject root. `Integral/{Basic,Tail}.lean` groups the first and second integral-tail theorems with their regular-variation consequences; both modules expose reusable results and remain outside `Lemmas/`. |
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
| `Mogulskii/Stable/RandomWalkBounds/FromIncrementLaw/Normal/HorizontalTube` | `Basic.lean` contains the core closed-tube rate, `Scales.lean` its scale specializations, and `EndpointWindow.lean` proves the endpoint-window rate using the event defined in the semantic `SmallDeviation/HorizontalTube/EndpointWindow.lean` module. `SourceCorridor.lean` owns the source-normalized constant-corridor event and both reusable inclusions between source corridors and the closed horizontal tube. The singleton endpoint-window corridor and its source-path inclusion remain theorem-specific under `Lemmas/EndpointWindowCorridor.lean`. The reusable unit-tube terminal-window construction is in `Topology/Cadlag/Skorokhod/PathClass/StepCorridor/TerminalWindow.lean`, and its all-exponent energy identity is in the corresponding `MeasureTheory/Measure/CadlagPath/PathClass/StepCorridor/TerminalWindow.lean`. |
| `Mogulskii/Stable/RandomWalkBounds/Source` | `Bounds/`, `Partition/`, and `PathClass/`; `Inputs.lean`, `Normalization.lean`, and `Realization.lean` remain at the source root. |
| `RandomWalk/Path/Interpolation` | `Finite/`, `Limit/`, and `Path/`; `Basic.lean` and `Scaling.lean` remain at the subject root. |
| `RandomWalk/Path/Block/Partition` | `Basic.lean`, `Core.lean`, and `Normalized.lean` give finite path-partition identities and corridor bounds; `TailMerged.lean` defines the quotient/remainder schedule and proves its endpoint and block-length identities. It is separate from the balanced partition in `Analysis/Asymptotics/Scale/BlockScale.lean`, which distributes the remainder among the blocks. |
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

The offspring-count module now owns the reusable splitting event
`offspringSplitSet := {ξ | 2 ≤ Step.childCount ξ}`, its identification with
`nontrivialSupport`, measurability, and the positive-mass consequence of an
expected child count greater than one. The exact-`N` initial-population entry
uses this shared event measurability result instead of carrying a duplicate
proof. The unused nonempty-offspring
specialization was removed from `InitialPopulation/Basic.lean`. The reusable
selected-population construction now lives in `Trajectory/Population.lean`.
The capacity-hitting proof has a dedicated `Trajectory/Lemmas/CapacityHit/`
chain: `Mark.lean` handles the selected address, fresh mark, and recurring
split event; `Growth.lean` handles the one-step cardinality bounds. The
generic bounded-growth saturation step remains private beside the principal
capacity-hitting theorem in `Trajectory/Hitting.lean`. A declaration-use
audit confirmed that the proof-chain modules are only imported within this
trajectory argument. `Hitting.lean` imports the offspring-count API directly;
`RunBridge.lean` imports the speed-transport theorem it uses directly rather
than receiving it through the hitting-time module.

## Same-stem files and directories

Mathlib permits a substantive `Foo.lean` interface beside `Foo/` when the
directory holds related component modules; the pinned Mathlib source has 113
such pairs, including `Tactic/Linarith.lean` beside `Tactic/Linarith/`. This
repository uses a stricter local organization rule for discoverability:
production and test source trees contain no same-level `.lean` file and
directory with the same stem. The initial project-tree inventory found such
pairs in production modules; their declarations now
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

The 2026-10-17 follow-up scan, including the split of the finite cyclic-path
interface into `Rotation/FinitePath.lean`, `Rotation/CyclicCover.lean`, and
`Rotation/FiniteProduct.lean`, found 1,450 production modules and 138 test
modules. The stable horizontal-tube lower-rate interface was subsequently
split into `Stable/Rate/Lower/{BlockProbability,Liminf,Positivity,Limit}.lean`;
the production count is now 1,453. Earlier batches grouped the Lemma 3.2 partition parameters, the
Lemma 3.3 jump-pattern and spatial-bin setup, the Lemma 3.5 staircase
parameters under their corresponding `Lemmas/` trees, and moved the generic
tail-merged schedule to the path-partition module.
Across both trees there are zero same-stem file/directory collisions, zero
directories with more than eight direct Lean files, and zero child filenames
repeating their immediate parent directory name. The vendored Mathlib and
BrownianMotion trees are excluded from these project-layout counts. The
`InitialPopulation/` and `Rademacher/` groupings above were checked separately.
In `InitialPopulation/`, `Basic.lean` exposes the exact-$N$ split-event and
speed-transport interfaces, while actual-population field, trajectory, and
speed proofs have their own subfamilies. In `Rademacher/`, `Basic.lean` gives
the Boolean-to-real increment encoding, `LastSignChange.lean` gives the
discrete terminal-segment construction, and `ConditionedPathLaw.lean` relates
the Boolean and real conditioned laws; `Terminal/` groups the terminal-path
law, mixture, and limit. These are distinct subject interfaces, not files
duplicating the `InitialPopulation` or `Rademacher` directory names. The scan
also caught and fixed `Analysis/Asymptotics/Scale/Scale.lean`, now
`Scale/Basic.lean`.

`BranchingProcessTest` mirrors production module names where it has
corresponding tests. Its larger `Stable` and `Branching` directories are test
collections, not public theorem layers. Test modules are grouped by the
mathematical API they exercise; this keeps test-only files out of production
`Lemmas/` trees while avoiding a large flat test directory.

## Public declaration headers

The 2026-10-17 interface pass added formula-bearing public declaration lists
to the reviewed modules in `Mogulskii/Spectral/Range/Rate/` and to
`Mogulskii/Spectral/Target/{Central,Coefficient,Expansion,ExtremalPair,LowerBound,Path}.lean`
and `Mogulskii/Spectral/Survival/Path.lean`. The current pass adds them to
`Mogulskii/RandomWalkBounds/Partition/{Corridor,Endpoint,Range,LowerProbability}.lean`;
the mirrored source-convention modules
`RandomWalkBounds/SourcePartition/{Basic,Events,LowerProbability}.lean` and
`RandomWalkBounds/SourcePartition/Lemmas/LowerGeometry.lean` now do the same. The sibling
`Partition/Lemmas/LowerGeometry.lean` and
`SourcePartition/Lemmas/LowerGeometry.lean` each document their single
proof-specific lemma. The stable finite-partition probability chain now also
lists its rate conclusions in `Stable/RandomWalkBounds/Partition/Probability.lean`
and `Stable/RandomWalkBounds/PartitionLower/{BridgeProduct,EnergyLower,FiniteProduct,Positivity,WidthRate}.lean`.
The source-convention rate entries now state the finite-partition and path-class
limits in `Stable/RandomWalkBounds/Source/Partition/Limit.lean` and
`Stable/RandomWalkBounds/Source/PathClass/Rate.lean`.
This pass also documents the pointwise encoding and pushforward law in
`Probability/Process/RandomWalk/Rademacher/Basic.lean`, the root-indexed
selected-population construction in
`InitialPopulation/Trajectory/Population.lean`, and the offspring-split,
capacity-hitting, and speed-transport interfaces in
`Probability/BranchingRandomWalk/Selection/NSelection/AsymptoticSpeed/InitialPopulation/Basic.lean`.
The offspring-count API now lists its child-count law, splitting event,
measurability, and positive-splitting-probability declarations in
`Probability/BranchingProcess/Offspring/Count.lean`; the trajectory-level
capacity-hitting entry lists its almost-sure capacity conclusion, while the
supporting selected-mark and cardinality-growth declarations are documented
in `InitialPopulation/Trajectory/Lemmas/CapacityHit/{Mark,Growth}.lean`.
These headers state the exact
declaration identifiers in their Lean namespace, the mathematical object or
estimate, and the assumptions that control each bound. The private path
equivalence helpers in `Target/Path.lean` remain outside the public list.
Targeted declaration-list checks found every public declaration in these
modules represented in its module docstring. The reviewed partition modules
and their dependent lower-bound targets build with the pinned Lean toolchain.
The fluctuation-theory review now lists and formulates every public
declaration in the seven audited ladder/positivity modules; a declaration-name
comparison found no missing or stale entries. Their module grouping and
source locations are recorded in the `RandomWalk/Fluctuation` row above.
The Brownian first-passage grid approximation header now also lists the
reusable path-agreement characterization
`firstPassageGridCeiling N r a f = i ↔ firstPassageGridCeiling N r a g = i`
when `f` and `g` agree through `r i`; `Brownian/Independence/FirstPassageGrid`
uses this interface to prove the selected index is a stopping time.
The convergence-in-distribution pass grouped its two approximation theorems under
`Probability/ConvergenceInDistribution/Approximation/` and added formula-bearing
public-declaration lists to `Basic.lean`, `DeterministicParameter.lean`, and
`Independence.lean`. The approximation and downstream Donsker/first-window modules
build with the pinned toolchain.
The Sparre--Andersen follow-up gives explicit declaration lists for the cyclic-gap and
composition-reindexing APIs. Proof-only event decomposition and block-factorization
steps are combined in `Composition/Lemmas/BlockProbability.lean`; the intermediate
event predicates and derivation lemmas are declared `private`, leaving only the
cyclic-gap endpoint identity public for the final composition formula. The recurrence
and finite-variance survival modules likewise expose their final theorem while keeping
coefficient bookkeeping and bound inductions private. All affected modules and their
downstream survival/transition callers build with the pinned toolchain.

A revised lexical scan, before the manual batches recorded below, found 8,580 top-level
declaration patterns and 1,062 modules whose module docstrings may omit at
least one declaration name. The revised scan accepts a fully qualified name
as well as its short name; the earlier count treated some fully qualified
names as missing. This remains a candidate count rather than a completed
audit: the scanner does not parse Lean syntax, can count declarations inside
`private section`s, can miss declarations introduced through attributes or
commands, and cannot assess whether a mathematical formula and its assumptions
are described accurately. The first manually reviewed batch adds
formula-bearing lists to `Combinatorics/Sequence/Block.lean`,
`Algebra/BigOperators/AdditivePath/Block.lean`,
`Algebra/Order/BigOperators/AdditivePath.lean`,
`Algebra/Order/BigOperators/WeightedSum.lean`, and
`Order/SetDissipate.lean`. The rest of the candidate modules remain to be
reviewed by semantic family. The next reviewed batch adds formula-bearing
lists to `Mogulskii/Partition/{Basic,Quantitative}.lean` and
`Mogulskii/Path/Tightness.lean`; their three module targets build successfully.
The deterministic address-and-genealogy pass now lists the public definitions
and relations in `Combinatorics/UlamHarris/{Basic,Generation,Order,Relation,Split}.lean`,
the step-field maps in `Combinatorics/BranchingWalk/StepField.lean`, and the
unmarked-process and genealogy projections in
`Combinatorics/Branching/{Basic,Map,Tree/Basic}.lean`. The stale IID module paths in
`ARCHITECTURE.md`, `FORMALIZATION_CHECKLIST.md`, and `MODULE_OWNERSHIP.md` were
updated after those modules moved into `IID/Blocks/`; the stable mapping
overview now points to the split regular-variation integral modules and the
norming module that owns `stableScaleTime_isRegularlyVaryingAtTop`.

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
the English translation title and DOI. The source records disagree on the
English issue number: MathNet lists volume 19, issue 1 (1975), while SIAM's DOI
page lists volume 19, issue 4 (1975). This repository follows the publisher's
record. The 2026-10-17 audit corrected 120 English-translation citations in 84
Lean and documentation files to volume 19, issue 4, while retaining the
Russian original as volume 19, issue 4 (1974). The source-by-source check confirms
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
Lemma A.7. The fluctuation modules also cite Chaumont--Doney's equation (2.2),
Section 2, and Lemma 5; Caravenna--Chaumont's definition (1.1), Lemma 2.1,
and equation (2.3); and Doney's Theorem 2, with publication details and DOIs.

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
The affine-tube spine estimates now identify Wang Yiyang's *Asymptotic Speed
of the N-Branching Random Walk with Infinite Offspring* (master's thesis,
Fudan University, 2026), Chapter 4, Lemma 4.2 for the small-drift segment
bound and Chapter 4, Lemma 4.5 for the terminally restricted corridor and
MRCA contributions. The previous generic `source` and bare lemma-number
references were replaced in the declaration docstrings.

The IID sequence audit grouped stopping-time, prefix-factorization, and conditional-block interfaces in `Probability/Sequence/IID/Blocks/`; these are complete reusable theorems, not theorem-specific proof fragments. Formula-bearing public theorem lists were added to the characteristic-function, filtration-independence, and law-identification modules. Direct users now import the renamed block paths.

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
| `RandomWalk/SmallDeviation/Drawdown` | `FiniteVarianceUpper/Basic.lean` formalizes Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.3 and its uniform consequence | `Path/Event/Drawdown.lean` owns the reusable finite-history drawdown predicates and their measurability. `FiniteVarianceUpper/TubeEvent.lean` owns the finite-pair and sequence-level horizontal drawdown tube events, which are the reusable semantic interface. The finite-prefix path, spatial-bin definitions, jump-pattern events, factors, and admissible pattern family are specific to Lemma 3.3 and live under `FiniteVarianceUpper/Lemmas/JumpPattern/`; the running maximum uses Mathlib's general `partialSups` API directly. `FiniteVarianceUpper/Lemmas/ConditionalBlocks.lean`, `Lemmas/JumpPattern/`, and `Lemmas/Rate/` contain the non-reusable conditional tube, rounded-maximum jump, union-bound, and rate proofs. General conditional event iteration was moved to `Probability/Process/Filtration/ConditionalBlocks.lean`; translation of finite interval events moved beside its definition in `Path/Window/Basic.lean`, and IID finite-block interval-law transfer moved to `Path/Block/Law/FiniteInterval.lean`. The generic quotient estimate for a horizon divided by a floor-rounded block length is in `Analysis/Asymptotics/Scale/BlockScale.lean`. DriftedTube now uses `Fin.partialSum` and finite sums directly instead of importing Drawdown's finite-sum aliases. `Scaling.lean` remains outside the proof tree because its scaling identities apply to general event sets. |
| `RandomWalk/SmallDeviation/Range` | Independent bounded-range and block-oscillation small-deviation estimates | `GaussianCover.lean` gives the finite translated-corridor cover; `BlockOscillation.lean` gives the source-corridor comparison; `Rate.lean` derives the resulting Gaussian range rate. The unused old block-reindex adapter was removed. These estimates are separate from the Lemma 3.3 drawdown proof, which uses Lemma 3.2 directly. |
| `RandomWalk/Fluctuation` | Random-walk records, ladder variables, and Sparre--Andersen identities | `Ladder/RecordLocalTime.lean` and `Ladder/Ascending.lean` define ascending records, local time, ladder times, and heights. `Ladder/Descending/` groups the reflected record/local-time interface, the descending renewal function, the finite-variance ladder-time finiteness result, and the stable-attraction tail theorem. `FiniteVarianceSignLimit.lean` remains at the subject root as the general Gaussian positivity-parameter and Spitzer-condition input. `SparreAndersen/Rotation/` contains the public cyclic-rotation cover and IID probability inequality; `Composition/Cyclic.lean` and `Composition/CyclicReindex.lean` expose the reusable gap-composition equivalence and arbitrary-weight sum reindexing, while the event-decomposition and block-probability proof chain is isolated in `Composition/Lemmas/`; `Survival/` contains the finite-variance lower bounds and recurrence interface. The declarations retain the `ProbabilityTheory.RandomWalk` namespace because each interface is stated for increment paths; the directory move groups the ladder-variable subject without changing ownership. The source citations identify Chaumont--Doney's equation (2.2) and Lemma 5, Caravenna--Chaumont's Lemma 2.1 and equation (2.3), and Doney's Theorem 2. |
| `Probability/BranchingRandomWalk/Population/Processes/Causal` | Causal genealogical populations and their capacity/path interfaces | The root keeps `Basic.lean`, `Predicate.lean`, and `Genealogy.lean` as the population construction, predicate selection, and samplewise genealogy interfaces. `Path/{Window,Bound}.lean` groups finite-history path representations and the reusable pathwise population bound. `Capacity/{Basic,FirstMoment,Spine}.lean` groups generic Markov capacity estimates and their first-moment/spine consequences. These are complete results for the causal-population interface, not fragments of one theorem-specific proof; `RelativePosition/` remains its own reusable path-position family. |
| `Probability/Process/RandomWalk/Kernel/Killed` | Reusable kernel interfaces for random walks killed on exit | `Basic.lean` defines the restricted transition kernel; `Comparison.lean` compares its survival mass; `Partition.lean` identifies equal-block survival with the path event. `Return/` groups endpoint distributions, target entrance, and terminal bridges; `Survival/` groups block iteration and uniform bounds. These are complete kernel statements reused by multiple small-deviation arguments, so they remain outside `Lemmas/`. |
| `Probability/Sequence/IID` | Canonical laws and reusable interfaces for independent identically distributed sequences | `Basic.lean`, `Law.lean`, `Filtration.lean`, `CharacteristicFunction.lean`, and `FiniteReindex.lean` remain direct peers for the canonical product law, law identification, prefix-filtration independence, characteristic functions, and finite coordinate symmetry. `Blocks/` groups the complete stopping-time, deterministic-prefix, and conditional block APIs; these are reusable mathematical results and therefore remain outside `Lemmas/`. |
| `Probability/Process/RandomWalk/Path/Block/Corridor` | Path events and finite-block comparisons for IID random walks | `Comparison.lean` gives the finite-cover measure inequality. `FiniteBridge.lean` adds a reusable `FiniteBridgeGeometry` record, derives uniform bridge mass from open-set path-law convergence, and turns it into the eventual probability and logarithmic-ratio bounds. Applications retain their source-specific corridor geometry in their subject modules. |
| `Probability/MeasureTheory/Asymptotics` | Asymptotic logarithmic bounds for probability-valued sequences | `FiniteProductRate.lean` turns eventual lower bounds by finite products of exponentials into a lower bound for the scaled logarithm of the target sequence. The result only assumes a finite index type, limits for the scaled counts, eventual nonnegativity of the rate, and values bounded by one; it is independent of random-walk and small-deviation structure. |
| `Probability/ConvergenceInDistribution` | Core weak-convergence interfaces | `Basic.lean`, `Portmanteau.lean`, `Mapping.lean`, `Independence.lean`, `DeterministicParameter.lean`, and `EscapingMixture.lean` remain direct peer interfaces: they define convergence compatibility, event bounds, continuous mappings, independent products, deterministic-coordinate products, and escaping finite mixtures. The related approximation principles are grouped under `Approximation/{AsymptoticEquivalence,Finite}.lean`; both are complete reusable results, so this semantic grouping does not use `Lemmas/`. The three core modules now list all public declarations and state their formulas and assumptions in the module headers.
| `Probability/Distributions/DomainOfAttraction` | General interfaces for normalized i.i.d. sums | `Basic.lean` defines attraction along explicit normalization and centering sequences; `Block.lean` transfers the limit to varying block lengths; `Centering.lean` derives zero mean when its hypotheses hold; `Normalization.lean` changes between eventually positive normalizations using `scaleₙ / scale'ₙ → r`, with limiting law pushed forward by `x ↦ r x`. This result applies to any probability limit and belongs at the general domain-of-attraction layer, not under stable norming or Mogulskii. |
| `RandomWalk/FunctionalLimit/Stable/PathLaw` and `PathLimit` | Fixed-grid laws and `J₁` limits for stable-domain random walks | `PathLaw/EndpointGrid.lean` handles the stable limiting grid, while `PathLaw/RandomWalkGrid.lean` derives the random-walk grid law directly from scalar domain-of-attraction data. `PathLimit/RandomWalk.lean` combines random-walk path-law convergence with the proved tightness criteria below, at, and above index one. The previous generic `Source` filenames were renamed to state the random-walk object explicitly. |
| `RandomWalk/SmallDeviation/Mogulskii/RandomWalkBounds/Partition` | Floor-rounded finite-partition bounds for normalized step corridors | `Corridor.lean` gives the grid-cell lengths and the upper range-probability product; `Range.lean` owns the IID block-oscillation and product estimates; `Endpoint.lean` owns the endpoint-core block event, its IID factorization, and knot induction; `LowerProbability.lean` assembles these into the corridor lower bound. `Lemmas/LowerGeometry.lean` contains only the theorem-specific deterministic gluing step from local block events to the global corridor event. It retains the `Discrete` namespace because the namespace describes the mathematical interface, while the move only groups the proof module. The lower-probability entry imports this helper ordinarily; its presence under `Lemmas/` indicates proof-chain role, while Lean declaration visibility is governed separately by `private` and the module import. |
| `RandomWalk/SmallDeviation/Mogulskii/Stable/Rate` | Exact centered horizontal-tube rate under a stable escape-rate hypothesis | `Upper.lean` gives the upper rate; `Lower/BlockProbability.lean` gives the endpoint-return block estimate; `Lower/Liminf.lean` derives strict-subtube and optimized lower rates; `Lower/Positivity.lean` supplies the real-log conditions used by the upper proof; `Lower/Limit.lean` identifies the limit. These complete mathematical interfaces remain outside `Lemmas/`. The partition probability module imports only `Lower/Positivity`, while the final rate test imports `Lower/Limit`. |
| `RandomWalk/SmallDeviation/Mogulskii/RandomWalkBounds/TerminalLeft/Partition` | Matching partition estimates for the source terminal-left convention | `Basic.lean` records the clipped terminal knot index and source cell lengths; `Events.lean` gives the selected-cell range upper bound; `LowerProbability.lean` is the lower-bound entry. `Lemmas/LowerGeometry.lean` contains the terminal-left deterministic gluing step and is imported ordinarily by the entry. The public interfaces remain beside the `Lemmas/` directory, and the `Discrete` namespace remains unchanged. |
| `RandomWalk/SmallDeviation/HorizontalTube` | `FiniteVarianceUpper/Basic.lean` formalizes Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.2 and its translated-interval form | The module namespace is `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube`, including `FiniteVarianceUpper/Lemmas/`. `BlockIteration.lean` owns the reusable killed-interval kernel identity, uniform block estimate, and finite-horizon iteration. The equal-partition and block-length parameters specific to Lemma 3.2, along with its cover, fixed-corridor rate, and rate assembly, are grouped under `FiniteVarianceUpper/Lemmas/Partition/`, `Lemmas/EqualPartition.lean`, and `Lemmas/Rate.lean`. `EndpointWindow.lean` defines the translated and normalized endpoint-window events; `FiniteVarianceLower.lean` owns the reusable endpoint-window consequence of Chapter 3, Lemma 3.1(ii), and `RealWidthLower.lean` supplies uniform real-width thresholds. Lemma 3.5's staircase-specific bins and endpoint fractions live under `DriftedTube/FiniteVarianceLower/Lemmas/Staircase/Setup/`; the finite-cover proof and selection lemmas are under `Lemmas/Staircase/Binning/`. |
| `RandomWalk/SmallDeviation/Entrance` | `FiniteVarianceEndpointCorridor.lean` and public interfaces with applications to multiple small-deviation arguments | `MovingCorridor.lean` owns the reusable moving-boundary path event and its constant-corridor inclusion, with no terminal-window parameter. `Edge/PrefixSelection.lean` retains the reusable positive-mass increment-window construction; its width inequalities specific to the Lemma 3.5 edge argument are in `Robust/Lemmas/Edge/PrefixGeometry.lean`. `Robust/Event.lean` defines the fixed `[2Δ/5,3Δ/5]` entrance event used in Chapter 3, Lemma 3.5; `Robust/Measurability.lean` proves its prefix-filtration measurability. The inclusion of the Donsker interior event in this narrower-window event is a theorem-specific step in `Robust/Lemmas/Event.lean`. The theorem-specific middle-start estimate, edge products, three-region minimum, and event inclusions remain under `Robust/Lemmas/`. The exponent-uniform assembly from forward and reflected transition-power bounds to a uniform robust-event lower bound is the reusable interface `Robust/PowerLower.lean`; it accepts every positive exponent and is used by the Appendix A.2, Lemma A.7 entrance estimate in the proof of Chapter 3, Lemma 3.5. The inverse-square estimate and polynomial-to-exponential bridge used only by Lemma 3.5 live under `DriftedTube/FiniteVarianceLower/Lemmas/Staircase/Concrete/EntranceBudget.lean`, with the inverse-square estimates private in that file. The unused broad-window power-assembly branch in `Edge` was removed. `Rotation/FinitePath.lean` defines the finite increment path and measurable corridor events; `Rotation/CyclicCover.lean` proves the deterministic path-ball cover by cyclic reindexing; `Rotation/FiniteProduct.lean` converts it to the finite-IID probability bound used by `NormalDomain.lean`. Generic finite-IID reindexing belongs to `Probability/Sequence/IID/FiniteReindex.lean`, and its measure-preserving finite-cover bound belongs to `MeasureTheory/OuterMeasure/Finite/Cover.lean`. The normal-domain entrance bound is still imported by the selected-population second-stage bridge and spine estimates. Lemma 3.5's meander entrance uses the distinct finite-horizon i.i.d. cyclic-rotation inequality in `Fluctuation/SparreAndersen/Rotation/Probability.lean`; `FunctionalLimit/Conditioned/Transition/SurvivalLower.lean` combines it with the Gaussian endpoint-sign limit to obtain the inverse-square width bound. The uniform real-width threshold is proved in the Lemma 3.5 staircase module. |
| `RandomWalk/FunctionalLimit/Conditioned` | Independent public interfaces by subject: `FirstWindow/`, `Meander/`, `Survival/`, and `Transition/` | `FirstWindow/Definition.lean` owns the prefix event and its measurability; `Selection.lean`, `Existence.lean`, `ConditionedLaw.lean`, `FiniteTime.lean`, `FinitePathLimit.lean`, `Absence.lean`, and `Limit.lean` remain direct complete constructions or limit results. The theorem-specific IID prefix/suffix factorization is grouped under `FirstWindow/Lemmas/BlockFactorization.lean`. The namespace remains `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned` because these declarations belong to the shared conditioned-random-walk interface; moving proof steps changes module organization, not mathematical ownership. `Meander/CorridorProbability.lean` contains the public open-corridor Portmanteau lower bound. `Survival/` contains the conditioned law and scaling. `Transition/Event.lean` owns the finite transition event, its normalized path corridor, equivalences, factorization, and diffusive horizon. The convergence-to-corridor and corridor-to-conditional-probability steps used in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5 are grouped under `Transition/Lemmas/CorridorProbability.lean`; `Transition/` contains the remaining meander limit and diffusive lower bounds. |
| `Probability/Process/Path`, `Probability/Process/TimeGrid`, and `Probability/Process/Brownian/AboveStart` | General path events, deterministic process-time grids, and their Brownian specializations | `TimeGrid/Ceiling.lean` gives the generic ceiling of an arbitrary extended nonnegative time functional by a finite monotone grid, with order, convergence, and measurability results; its selector uses Mathlib's `MeasureTheory.hittingBtwn`. `TimeGrid/UnitInterval.lean` and `TimeGrid/Expanding.lean` provide deterministic grids, while `TimeGrid/Dense/NonnegativeRationals.lean` provides a countable dense set of observation times. None depends on path or Brownian structure. `Path/FirstPassage/GridApproximation.lean` specializes the generic ceiling interface to continuous-path first passage and owns path-locality and reflection-continuity results. Brownian reflection at the selected time is in `Brownian/Reflection/FirstPassage/GridLaw.lean`; finite path observations use `hittingBtwn` directly in `Grid.lean`. `Path/FirstPassage/` also groups descending-hitting-time, reflection, and restart interfaces. `Path/AboveStart/FirstWindow/` groups path-level first-window results; `Brownian/AboveStart/FirstWindow/` keeps the finiteness and first-window-time continuity entries at its root; `Shift/` groups the uncentered, centered, finite-horizon, and cutoff-limit path-shift continuity results, which form one coherent path-transform family. Random-walk path foundations are grouped into `Path/Adapted/` (filtration and martingale), `Path/Event/` (drawdown, survival, oscillation, and last sign change), and `Path/Representation/` (càdlàg paths, interpolation, and scaling); the `Basic`, `Window`, and `Skorokhod` entry modules remain at the root. |
| `Topology/Cadlag/Skorokhod` | Reusable topology and geometry for càdlàg paths with the Skorokhod metric | Public interfaces are grouped under `Compactness/`, `Corridor/`, `EDistance/`, `Evaluation/`, `Maps/`, `Oscillation/`, `Path/`, and `TimeChange/`. `Topology.lean` remains the subject-level topology interface. `TimeChange/Limit/` groups the summable-distortion convergence chain; `EDistance/Logarithmic/Completion/` groups the aligned Cauchy construction, subsequence extraction, limit identification, and completeness theorem. These are complete reusable convergence results, so they are grouped by mathematical role rather than under `Lemmas/`. |
| `BranchingProcessTest` | Tests for the production library | Test modules are grouped by topic. Mogul'skii tests use `Mogulskii/{Axiom,Path,PathClass,Rates,Regression}/`; stable tests use `Attraction/`, `PathLaw/`, `RandomWalk/`, and `SmallDeviation/`; restart tests use `Branching/Restart/Trial/` and `Branching/Restart/Lineage/`; Skorokhod tests are grouped by topology operation. `scripts/run-all-lean-tests.py` and CI log paths follow these locations. |
| `Combinatorics/BranchingWalk/Basic` | Shared data and basic branching-walk operations | `Genealogy/` contains ancestor, descendant, and generation-size results; `Position/` contains displacement and position maps; `Sibling/` contains parent/sibling relations and closure properties; `Survival/` contains realized-particle and path-survival predicates; `Ordering/` contains orderability. `Definitions.lean` and `Map.lean` remain directly under `Basic/` as shared foundations. |
| `Combinatorics/BranchingWalk/Selection/NSelection` | Deterministic capacity-`N` selection and its induced walks | `Mechanism/` contains the selection rules, rank and value interfaces, and matching criteria; `Walk/` contains the bounded walk, its cloud, generation frontiers, and speed; `Coupling/` contains the coupling modules directly, with callers importing the specific result modules. `Basic.lean` remains the mechanism definition. |
| `Probability/BranchingRandomWalk/Spine` | Spine random walks, many-to-one identities, and tube moments | `ManyToOne/`, `RandomWalk/`, `PointMeasure/`, and `Tilted/` group the corresponding public constructions. `Path/` keeps its core interfaces at the root and groups decomposition, many-to-one, and second-moment results by subject. `Tube/` groups corridor, MRCA, and second-moment estimates. The declaration namespaces remain rooted at `ProbabilityTheory.BranchingRandomWalk.Spine` to preserve the existing API; only module paths changed. |
| `Probability/RandomMeasure/Poisson` | Poisson random measures and their public probability interfaces | `Integration/`, `Intensity/`, `JumpPath/`, and `Realization/` group integration identities, support and time-mark facts, path bounds, and finite-jump configurations. `Basic.lean`, `PointFamily.lean`, and `Superposition.lean` remain the direct core interfaces. The declarations retain the `ProbabilityTheory` namespace. |
| `Probability/Process/Brownian` | Brownian-process construction, continuous path laws, and support | `Construction/` groups existence and modification inputs; `PathLaw/` groups continuous versions and path-space laws; `Scaling/`, `Marginal/`, and `Support/` own the corresponding interfaces. `Reflection/` is divided into `Path/`, `FirstPassage/`, and `Descending/` families. `FirstPassage/Grid.lean` uses Mathlib's generic `hittingBtwn` for finite observations; `GridLaw.lean` contains the Brownian-law theorem for the separate path first-passage grid approximation. |
| `Probability/Process/Path/Skorokhod/Corridor/UniformBlocks` | Finite uniform partitions of path corridors | `Independence.lean` states mutual independence of the canonical rational block paths and independence of a prefix path from its next block for any process with independent increments; `Stationarity.lean` identifies translated block laws under stationary independent increments. `Feedback/Basic.lean` defines the sign-selected block and prefix events and their pathwise identities; `Feedback/FullPath.lean` gives the reusable càdlàg transfer from rational-coordinate bounds to a full-path tube. These statements belong to the named path construction, not to stable-process small-deviation modules. |
| `Probability/Process/RandomWalk/FunctionalLimit/Stable` | Stable-domain path-law convergence and tightness | `PathLaw/` groups endpoint-grid identification, subsequential law construction, process-law construction, and convergence. `Tightness/` groups block tails, local oscillation, partition bounds, compact-range control, and the resulting tightness theorem. The finite-dimensional endpoint theorem and centering conditions remain at the subject root. |
| `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Spectral/Range` | Rademacher range small-deviation estimates from spectral interval bounds | `Blocks/` contains the one-block Donsker bounds; `Corridor/` contains the finite Brownian cover and killed-corridor comparison; `Rate/` contains the Brownian range asymptotics, small-width limit, and sharp upper rate. Its parameter selection and fixed-cover logarithmic transfer are proof-specific and live under `Rate/Lemmas/`. `Basic.lean` defines integer path coordinates, while `Probability.lean` retains the finite-time translated-interval cover. |
| `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Rate` | Public normal-domain small-deviation rate results | `Endpoint/` groups endpoint bands, windows, and parameter selection; `Endpoint/Selection/Basic.lean` is the public sharp-rate conclusion, while its floor choices and fixed-parameter proof step are in `Endpoint/Selection/Lemmas/FixedParameters.lean`. `Partition/` groups finite covers and partitions; `Bounds/` groups interior, lower, upper, and variance estimates. The declarations keep their existing Mogulskii namespace because their mathematical ownership is unchanged. |
| `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Spectral` | Spectral estimates for the killed symmetric walk, including diffusive Brownian corridor and endpoint-window bounds | `Kernel/` defines the finite killed transition; `Decomposition/` gives its sine basis, modes, and target-set expansion; `Target/` owns parity-compatible central targets, their principal-mode mass bounds, and the path-event interpretation. These target estimates are parameterized by the target set, interval width, and block scale, so they remain reusable interfaces. `Survival/` groups path-survival bounds; `Scaling/` and `Rate/` contain the diffusive logarithmic limits and analytic asymptotics; `Diffusive/` transfers the spectral lower bound through Donsker convergence to Brownian corridors and return kernels. The finite-cover range upper bound remains in the separate `Range/` family. `Basic.lean` is the core interface, and declarations retain the Mogulskii spectral namespace. |
| `Probability/Process/RandomWalk/Fluctuation/SparreAndersen` | Reusable finite IID fluctuation identities and survival estimates | `Rotation/` contains the cyclic cover and probability inequality; `Composition/` contains block factorization and the finite composition identity; `Survival/` contains the coefficient recurrence and finite-variance lower bound. These are general mathematical results and remain outside `Lemmas/`. |
| `Probability/Process/RandomWalk/Rademacher` | Results for the simple symmetric random walk | `Basic.lean`, `ConditionedPathLaw.lean`, and `LastSignChange.lean` are peer interfaces for the walk, its conditioned path law, and its last-sign-change index; `Terminal/` groups the terminal-path construction and convergence steps. |
| `BranchingRandomWalk/Selection/NSelection/AsymptoticSpeed/InitialPopulation` | Initial-population inputs to selected-walk speed estimates | `Basic.lean` is the exact-$N$ split-event and speed-transport interface; `Field/` and `Speed/` group the source field and speed estimates. In `Trajectory/`, `Population.lean` owns the selected-population construction, `Hitting.lean` is the capacity-hitting entry theorem, and `Lemmas/CapacityHit/{Mark,Growth}.lean` contains its proof-specific mark and cardinality-growth chain. |
| `Selection/NSelection/EndpointDeviation` | Endpoint deviations of the selected population, including estimates that admit reflection | `Endpoint/` separates minimum, positive-moment, and sequence results. `Roots/`, `Drawdown/`, and `Rate/` group root estimates, population/spine drawdown bounds, and rate budgets. `FirstStage/LowCountPower.lean` states the first-stage population low-count estimate; its one-use corridor budget and PZ rate assembly are under `FirstStage/Lemmas/`. `FirstStage/` and `SecondStage/` name the proof stages directly instead of encoding the positive exponent parameter in a folder name. `Population/` and `SecondStage/` retain their theorem families; the directory name does not impose a right-hand orientation. |
| `Selection/NSelection/AsymptoticSpeed` | Speed-limit statements and the selected-population speed proof | `Limit/` groups the almost-sure product and subadditive limit results; `Selection/BlockComparison.lean` and `InitialPopulation/Speed/Basic.lean` state their respective public conclusions. `InitialPopulation/Basic.lean` is the entry module for the initial-population argument; `Field/`, `Trajectory/`, and `Speed/` group its field, hitting-time, and speed-transfer interfaces. `Environment/` and `Selection/` hold the remaining supporting constructions. |
| `Mogulskii/RandomWalkBounds` and `Mogulskii/Stable/RandomWalkBounds` | Random-walk finite-block bounds and stable-domain random-walk rates | The normal-domain root separates Donsker endpoint, endpoint-band geometry, horizontal tubes, and source-partition arguments. Stable random-walk bounds group `Bridge/`, `Endpoint/`, `Partition/`, `PathClass/`, and `TerminalLeft/`; `Partition/Lower/` contains the complete lower-rate interfaces, while upper and limit conclusions stay in their corresponding `Partition/` modules. The source-convention lower-rate chain is under `TerminalLeft/Partition/Lower/`, where it keeps the distinct terminal-left path encoding. `Bridge/Events.lean` defines the source corridor events and interior bridge centers that occur in the equation-(34) theorem interfaces. `Bridge/TerminalLeftAsymptotics.lean` proves the equation-(34) bridge estimate from explicit entrance and path-limit hypotheses, while `Bridge/CdfEntrance.lean` specializes it to the source CDF sign condition and exposes the resulting bound. The reusable finite-bridge geometry record and probability comparisons live at `Probability/Process/RandomWalk/Path/Block/Corridor/FiniteBridge.lean`; source-specific finite-cover geometry, bridge cells, entrance positivity, and terminal-left decay derivations remain under `Bridge/Lemmas/`. The stable-process estimates remain in their own owner directory. `Stable/RandomWalkBounds/FromIncrementLaw/` separates `Normal/`, `Path/`, and `Stable/` adapters, with `HorizontalTube/` holding the finite-variance tube interfaces. `Stable/Scale/Basic.lean` owns the two-scale condition and rate consequences; `Stable/Scale/Rate.lean` owns block-length asymptotics. Gaussian modules remain divided into `Gaussian/Blocks/` and `Gaussian/Path/`. `FunctionalLimit/Donsker/Entrance/` owns the Brownian middle-start corridor and uniform diffusive entrance estimates. |
| `Analysis/Asymptotics/Power` | General real-power comparisons for extended nonnegative quantities | `ENNRealRatio.lean` combines real-power lower and upper bounds into a quotient bound. It depends only on `ENNReal` and real powers, so the former `Probability/MeasureTheory/Moments/PowerRate.lean` was moved here from its one-use Paley–Zygmund caller. |
| `Analysis/Asymptotics/Scale` | Reusable deterministic scale tools | `Basic.lean` defines the common small-deviation scale relation; `InverseScale.lean` handles generalized inverses and their subdiffusive rates; `BlockScale.lean`, `ShiftedFloor.lean`, and `IntermediatePowerBlock.lean` cover integer block rounding and intermediate block scales; `Sampling.lean` transfers rates along selected time intervals; `SlowDiagonal.lean` and `Tolerance.lean` provide real-valued diagonal and error-threshold selections. All eight direct modules are distinct reusable interfaces, so they remain as peers at this level. |
| `Analysis/Asymptotics/RegularVariation` | Regular variation, slow variation, and Karamata-type consequences | `Basic.lean`, `Uniform.lean`, `AsymptoticInverse.lean`, `LowerPower.lean`, `MonotoneDensity.lean`, and `SlowScale.lean` remain at the subject root. `Integral/{Basic,Tail}.lean` groups the first and second integral-tail theorems with their regular-variation consequences; both modules expose reusable results and remain outside `Lemmas/`. |
| `Stable/SmallDeviation/Blocks/Lower` | Lower block estimates | `Assembly/`, `Binning/`, `Bounds/`, `Entrance/`, and `Return/` group the distinct construction steps. `Entrance/PoissonModel.lean` owns the stable `α < 1` positive entrance theorem; it hides the chosen Lévy--Khintchine triple and exposes only the stable-process and CDF assumptions. `Lemmas/ReturnScale.lean` holds the first-uniform-block specialization used by the lower-bound proofs; arbitrary-horizon stable scaling stays at the `Blocks/` level. `Feedback/` contains the stable short-block scaling and entrance consequences; the adaptive finite-block probability and path-tube implications now live with generic uniform-block path results. Stable-law adapters are limited to block laws and estimates whose statements actually use stability. |
| `BranchingRandomWalk/Restart/RootedTrial` | Rooted-trial restart and coupling | Finite-slot and reserve arguments have their own subdirectories. |
| `Combinatorics/BranchingWalk/Step` | Deterministic branching-step operations | The root keeps `Basic`, `Map`, `Measurability`, and `Relation`. Ordering properties and ranks are under `Ordering/`; slot selection and sibling closure are under `Selection/`; potential and point-measure operations are under `Measure/`; generation-local updates are under `Generation/`. |
| `Probability/BranchingRandomWalk/Step` | Random step presentations, fields, and laws | Coordinate presentations and their constructors/maps are under `Presentation/`; field operations under `Field/`; probability laws under `Law/`; measurable ordering under `Ordering/`; point-measure observations under `PointMeasure/`. Root-indexed position measurability remains under `Position/`. |

## Abstraction review: stationary increment path laws (2026-10-19)

This review was triggered by repeated use of translated block-path laws. The
checked Mathlib revision is
`380f2aafb622cb2c1c93dac545b6389083c68c51`. The official
[independent-increment API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Process/HasIndepIncrements/Basic.html)
defines independence of increments along every finite monotone time grid.
The official
[finite-dimensional-law API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/FiniteDimensionalLaws.html)
characterizes equality of process laws by equality of all finite-dimensional
distributions. These are the general ingredients used here; neither API
packages equal-duration time changes of a process with stationary independent
increments. The local
`Probability.Process.IndepIncrements.FiniteDimensional` API already proves
function-valued law equality from matching increment laws and zero starts, and
`Probability.Process.IndepIncrements.DisjointPaths` already gives independence
for arbitrary observed path coordinates on adjacent intervals and for finite
monotone partitions. The literature uses stationary independent increments as
the defining increment structure of a Lévy process; see the
[Cambridge excerpt of Sato, *Lévy Processes and Infinitely Divisible
Distributions*](https://assets.cambridge.org/97811076/56499/excerpt/9781107656499_excerpt.pdf).

The resulting public path-law theorem is
`HasIndepIncrements.process_identDistrib_of_sameDuration_timeChanges` in
`Probability/Process/IndepIncrements/PathLaw/StationaryTimeChange.lean`. It
assumes independent increments, stationary increments, monotone maps
`τ, τ' : I → T`, and
`τ t - τ s = τ' t - τ' s` whenever `s ≤ t`; it concludes equality in law of
the centered paths
`q ↦ X (τ q) - X (τ ⊥)` and
`q ↦ X (τ' q) - X (τ' ⊥)`, with almost-everywhere measurability of those path
maps. Its time type is an ordered additive commutative monoid with ordered
subtraction, its index is any linearly ordered type with a least element, and
its state is a measurable additive commutative group. The proof reduces path
increments to equal-duration one-increment laws and then applies the local
finite-dimensional uniqueness theorem. It needs no zero-start, càdlàg, stable,
moment, or scaling assumption. This is the most abstract useful form found:
it adds the equal-duration path-law operation absent from Mathlib while
retaining the standard hypotheses that make its proof work.

The complete-segment corridor consequences live beside their event semantics
in `Probability/Process/Path/Skorokhod/Corridor/SegmentStationarity.lean`.
They additionally require almost-surely càdlàg paths to pass from rational
coordinates to all times, but do not require a Lévy or stable-process record.
For finite rational uniform partitions, the named block-path interface in
`UniformBlocks/Independence.lean` specializes the more general
`DisjointPaths` results. The two retained statements expose canonical
partition paths used by the corridor factorization and upper-block arguments;
the unused adjacent-block specialization was removed because
`indepFun_adjacentPaths` already states the more general result. The
stable-only block-law wrapper under `Stable/SmallDeviation/Blocks/Lemmas/`
was also removed: its callers now use the general rational-block law directly,
supplying only the independent- and stationary-increment properties inherited
from the stable process. The stable-only prefix/next-block independence alias
was removed for the same reason; its callers invoke the general
`UniformBlocks/Independence` theorem. The entrance/continuation independence
calculation remains private in `EntranceFactorization.lean` because only that
file's event-factorization proofs use it.

The same review compared the arbitrary-horizon return-corridor scaling laws in
`Blocks/ReturnScale.lean` with their first-uniform-block specializations. The
arbitrary-horizon centered-path and corridor identities remain at the Stable
small-deviation block level as complete scaling results. The first-block
return identity is used only by lower block-bound proofs, so it now lives in
`Blocks/Lower/Lemmas/ReturnScale.lean`; it is derived from the arbitrary-horizon
identity and the canonical first-block path equation. The unused first-block
specialization for the left-open endpoint convention, the unused forward
orientation, and a positivity corollary that only rewrote an existing scaling
identity were removed. The proof-only `ReturnScale` dependency of
`EntranceScaling.lean` is now an ordinary import; its public imports name the
Stable process and path-event interfaces appearing in its theorem statements.

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
| `Stable/SmallDeviation/PathClass/StepCorridor/Partition` | `Core/`, `Lower/`, and `Upper/`. The deterministic endpoint-core plus finite inner-cell geometry now lives at its semantic owner, `Topology/Cadlag/Skorokhod/PathClass/StepCorridor/Partition/LowerGeometry.lean`; the stable `Lower/Geometry.lean` is reserved for cell events and their pathwise concatenation. The one-use radius-contraction step is under `Lower/Lemmas/CoreShrink.lean`. |
| `Stable/SmallDeviation/Blocks/Lower` | `Assembly/`, `Binning/`, `Bounds/`, `Entrance/`, `Return/`, and `Lemmas/`. |
| `RandomWalk/SmallDeviation/Mogulskii` | `Theorems.lean` is the Lean import entry for the original paper's Theorems 1–4. Its public imports group the formalized interfaces for Theorem 1 (discrete random walk), Theorem 2 (strictly stable process), and Theorem 3 (Gaussian/finite variance); the module documentation records their formulas and declaration names. Theorem 4, the full continuous-time source-process rate of Section 5, is not formalized yet and is explicitly marked pending, with its missing process-level inputs in `docs/MOGULSKII_PROCESS_THEOREM_4_PROOF_ROUTE.md`. Keep this as a Lean import module, not a Markdown index. Supporting declarations stay in semantic families rather than catch-all root `Definitions/` or `Lemmas/` directories: `Path/` owns path encodings and corridor events; `Scale/` owns diffusive and stable normalization; `Partition/` owns discrete finite-partition estimates; `Stable/` and `Gaussian/` contain stable-domain and finite-variance specializations; `RandomWalkBounds/` assembles endpoint and corridor probability bounds; `Rate/` groups the normal-domain rate arguments; and `Spectral/` owns the killed symmetric-lattice spectral route. Reusable mathematical results remain in these subject modules; theorem-specific derivation steps stay in nested `Lemmas/` modules. `Gaussian/Blocks/` contains complete finite-dimensional block-limit results; the finite Gaussian-product parameter choices used only while assembling the lower-bound proofs are grouped under `Gaussian/Blocks/Lemmas/`. `Gaussian/EscapeConstant.lean` is the Brownian escape-constant entry, and its one-use Rademacher-to-tube bridge lives under `Gaussian/Lemmas/NormalConstant.lean`. `Blocks/Uniform.lean` gives finite-reference block-survival estimates. `Return/Partition.lean` gives finite-partition return-kernel lower bounds, and `Return/Uniform.lean` lifts these to uniform starting-point bounds and iterates the return kernel. The declarations in these subject folders are supporting APIs; the original-paper theorem entry remains `Theorems.lean`. |
| `BranchingRandomWalk/Selection/NSelection/AsymptoticSpeed` | `Limit/` and `Selection/` group the main speed argument; `InitialPopulation/Basic.lean` remains the initial-population entry, with `Field/`, `Trajectory/`, and `Speed/` subfamilies. |
| `Mogulskii/Stable/RandomWalkBounds/FromIncrementLaw` | `Normal/`, `Path/`, and `Stable/`; `Normal/HorizontalTube/` groups the index-two finite-variance tube rate, endpoint-window forms, and their proof lemmas with the other normal-domain results. |
| `Mogulskii/Stable/RandomWalkBounds/FromIncrementLaw/Normal/HorizontalTube` | `Basic.lean` contains the core closed-tube rate, `Scales.lean` its scale specializations, and `EndpointWindow.lean` proves the endpoint-window rate using the event defined in the semantic `SmallDeviation/HorizontalTube/EndpointWindow.lean` module. `TerminalLeftCorridor.lean` owns the terminal-left constant-corridor event and both reusable inclusions between terminal-left corridors and the closed horizontal tube. The singleton endpoint-window corridor and its terminal-left path inclusion remain theorem-specific under `Lemmas/EndpointWindowCorridor.lean`. The reusable unit-tube terminal-window construction is in `Topology/Cadlag/Skorokhod/PathClass/StepCorridor/TerminalWindow.lean`, and its all-exponent energy identity is in the corresponding `MeasureTheory/Measure/CadlagPath/PathClass/StepCorridor/TerminalWindow.lean`. |
| `Mogulskii/Stable/RandomWalkBounds/TerminalLeft` | `Bounds/`, `Partition/`, and `PathClass/`; `Inputs.lean`, `Normalization.lean`, and `Realization.lean` remain at this source-convention root. |
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
| `Distributions/Stable/Attraction/Norming` | `Basic.lean`, `Inverse.lean`, `Compatibility.lean`, `Centering.lean`, `Mogulskii.lean`, `Tail.lean`, and `UniformTail.lean` remain at the subject root; Gaussian and index-two specializations are under `SpecialCases/`. `Mogulskii.lean` contains the theorem-specific passage to Mogul'skii's source time normalization and its index-one centering transfer; its rounded index sequence and asymptotic lemmas are private. The general normalization-change theorem is in `Distributions/DomainOfAttraction/Normalization.lean`. |

The finite-dimensional Gaussian block-vector limit in
`Mogulskii/Gaussian/Blocks/BlockVector.lean` specializes the general
`RandomWalk/FunctionalLimit/FiniteDimensional/IndependentBlocks.lean`
consecutive-block theorem. This keeps the generic independence and
coordinate-limit assembly at the reusable functional-limit layer while the
Mogulskii module supplies its diffusive scale and Gaussian parameters.

Within `Mogulskii/Spectral/Target/`, the target indicator and its full
finite-dimensional spectral expansion remain in `Expansion.lean`, while
`LowerBound.lean`, `Central.lean`, `Path.lean`, `Corridor.lean`, and
`Bands.lean` expose complete target-mass and path-event estimates. The sine
coefficient calculations in `Lemmas/Coefficient.lean` are used only by the
extremal-mode argument, so they live under the target proof's `Lemmas/`
directory and are ordinary-imported by `ExtremalPair.lean`.

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
the count was 1,453 before the current geometry split. The current worktree
scan finds 1,466 production Lean files and 138 test files, including untracked
work in progress. The largest production directory has eight direct Lean
files. Earlier batches grouped the
Lemma 3.2 partition parameters, the Lemma 3.3 jump-pattern and spatial-bin
setup, the Lemma 3.5 staircase
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
`RandomWalkBounds/TerminalLeftPartition/{Basic,Events,LowerProbability}.lean` and
`RandomWalkBounds/TerminalLeftPartition/Lemmas/LowerGeometry.lean` now do the same. The sibling
`Partition/Lemmas/LowerGeometry.lean` and
`TerminalLeftPartition/Lemmas/LowerGeometry.lean` each document their single
proof-specific lemma. The stable finite-partition probability chain now also
lists its rate conclusions in `Stable/RandomWalkBounds/Partition/Probability.lean`
and `Stable/RandomWalkBounds/Partition/Lower/{EnergyLower,Positivity,WidthRate}.lean`; their proof-specific endpoint-core product construction is under `Partition/Lower/Lemmas/BridgeProduct.lean`, and the terminal-left counterpart is under `TerminalLeft/Partition/Lower/Lemmas/BridgeProduct.lean`. The finite-product logarithmic-rate transfer is at its probability-asymptotics owner, `Probability/MeasureTheory/Asymptotics/FiniteProductRate.lean`.
The source-convention rate entries now state the finite-partition and path-class
limits in `Stable/RandomWalkBounds/TerminalLeft/Partition/Limit.lean` and
`Stable/RandomWalkBounds/TerminalLeft/PathClass/Rate.lean`.
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
The path first-passage grid approximation now specializes the generic
`Probability.Process.TimeGrid.Ceiling` interface, whose arbitrary-domain
time functional is rounded up to a finite monotone `ℝ≥0` grid. Its header
lists the reusable path-agreement characterization
`firstPassageGridCeiling N r a f = i ↔ firstPassageGridCeiling N r a g = i`
when `f` and `g` agree through `r i`; `Brownian/Independence/FirstPassageGrid`
uses this interface to prove the selected index is a stopping time.
This pass also completed the declaration lists for the affine-tube spine
second-moment modules `Spine/Tube/SecondMoment/OneGenerationTail.lean` and
`Spine/Tube/MRCA/PairContribution.lean`, covering all 37 and 32
module-visible declarations respectively, with their corridor, moment, and
MRCA formulas. A name comparison confirms that each declaration appears in
its module header.
The same follow-up found and fixed missing declaration lists in the other nine
`Spine/Tube` modules: `Corridor/{FiniteVariance,IndependentRoot,PairBound,SecondMoment}.lean`,
`MRCA/{ActualContribution,Expansion}.lean`, and
`SecondMoment/{Basic,MultiGeneration,TwoStage}.lean`. Their 39 public
definitions and theorems now have named mathematical descriptions; the
directory scan confirms that every public declaration across `Spine/Tube/`
appears in its module header.
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
Russian original as volume 19, issue 4 (1974). A later working-tree edit
reintroduced issue 1 in 130 citation occurrences across 90 files; this pass
restores the publisher's issue 4 in those files. The source-by-source check confirms
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
The affine-corridor event-transfer helper now describes only its deterministic
inclusion; its former bare “Lemma 2.3” mention did not identify a source result
used by that helper. The finite-variance estimate that supplies the drawdown
bound retains its explicit Wang thesis Chapter 3, Lemma 3.3 and Aïdékon--Hu
Lemma 2.3 references in its owning module.

The IID sequence audit grouped stopping-time, prefix-factorization, and conditional-block interfaces in `Probability/Sequence/IID/Blocks/`; these are complete reusable theorems, not theorem-specific proof fragments. Formula-bearing public theorem lists were added to the characteristic-function, filtration-independence, and law-identification modules. Direct users now import the renamed block paths.

## Abstraction research: stable constant-corridor rate

A cross-module reuse observation prompted a generality review of
`Probability/Process/Path/PathClass/StepCorridor/Probability/Rate/StableConstantCorridor.lean`.
The pinned Mathlib API supplies weak convergence of probability laws and the
continuous mapping theorem in
[`MeasureTheory.Function.ConvergenceInDistribution`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/ConvergenceInDistribution.html),
but no large-deviation or small-deviation principle for the logarithmic
probability of a shrinking path corridor. The local stable-process layer
already supplies the more general reusable hypotheses and shifted-corridor
rate through `IsStableLevyProcess.exists_shiftedCorridor_escape_rate` and
`HasStableProcessEscapeRate`.

The literature has broader results along different axes: Elena Shmileva,
*Shifted small deviations and Chung LIL for symmetric alpha-stable processes*
(arXiv:0811.2583, 2009), treats arbitrary continuous shifts for symmetric
stable processes with index in `(1, 2)` in the uniform topology; Frank Aurzada
and Steffen Dereich, *Small deviations of general Lévy processes* (Annals of
Probability 37 (2009), 2066–2092, arXiv:0805.1330), treats centered
supremum-norm small deviations for general real-valued Lévy processes. The
first result imposes symmetry and an index range, while the second studies a
centered two-sided supremum corridor. Neither directly subsumes the local
finite, possibly asymmetric constant-corridor statement under the stable path
law assumptions.

The local theorem is therefore kept as a complete constant-corridor
specialization at the path-class rate boundary, built on the stable-process
interfaces above. Its proof-specific scalar rescaling remains local. The
audit removed the duplicate import and the unused public
`scaledPathConstantCorridorEvent` wrapper: the theorem now states its result
using the existing `scaledConstantCorridorEvent`, which is the canonical event
for these bounds. This review records why the result remains a specialization
and does not introduce a second public general-purpose small-deviation API.

## Abstraction research: stationary increments and translated block laws

The uniform-block path-law proof was reviewed against its actual mathematical
hypotheses before promoting its interface. Mathlib's pinned
[`HasIndepIncrements` source](https://github.com/leanprover-community/mathlib4/blob/021c46bdd042f67b538b9f9871d556a93713a9a9/Mathlib/Probability/Independence/Process/HasIndepIncrements/Basic.lean)
defines independent increments for a process over a preorder, but has no
stationary-increment property or translated-process law theorem. Joseph C.
Watkins, *Stochastic Processes in Continuous Time*, Definition 2.1, p. 12,
states stationary increments and independent increments as separate
properties of a process; stationary increments say that the law of
`X_{t+s} - X_t` is independent of `t` ([lecture notes](https://math.arizona.edu/~jwatkins/notesc.pdf)).
The broader time statement below is derived from the ordered additive-time
hypotheses, rather than attributed to Watkins's real-time definition.

The Lean API therefore records stationary increments independently in
`Probability/Process/StationaryIncrements/Basic.lean`, with only an additive
time monoid and subtraction on the state. The finite-dimensional law API in
`Probability/Process/IndepIncrements/FiniteDimensional.lean` takes values in a
measurable additive commutative group with measurable addition. Its
finite-dimensional position-law theorem uses an explicit anchor instead of
requiring a least time. The translated-increment law is stated for an ordered
additive commutative time monoid with `PartialOrder`, `AddLeftMono`,
`ExistsAddOfLE`, `Sub`, and `OrderedSub`. These assumptions express the two
steps used in the proof: left translation preserves monotone grids, and the
interval from `q` to `r` has length `r - q`. The duration assumptions use
Mathlib's `ExistsAddOfLE` and `OrderedSub` interfaces
([`ExistsAddOfLE`](https://github.com/leanprover-community/mathlib4/blob/021c46bdd042f67b538b9f9871d556a93713a9a9/Mathlib/Algebra/Order/Monoid/Unbundled/ExistsOfLE.lean),
[`OrderedSub`](https://github.com/leanprover-community/mathlib4/blob/021c46bdd042f67b538b9f9871d556a93713a9a9/Mathlib/Algebra/Order/Sub/Defs.lean)).
The theorem uses only independent and stationary increments; no càdlàg,
stochastic-continuity, or stable-law assumption enters its statement. The
rational uniform-block path theorem keeps real-valued path geometry, but
assumes only these two increment properties and coordinate measurability. Its
stable-process corollary remains at the stable small-deviation boundary as an
adapter.

This placement follows the mathematical dependencies rather than the number
of clients: the standalone stationary-increment predicate and state-group
finite-dimensional law are reusable process results, while the rational tube
event remains a real path-space specialization. The comparison also prevents
the stronger `IsLevyProcess` bundle, whose càdlàg component is unused, from
becoming the hypothesis of the generic block-law theorem.

## Abstraction research: finite cyclic-gap expansion

The cross-module use of the finite cyclic-gap formula triggered a review of
its mathematical generality before deciding its placement. Bauer, Godrèche,
and Luck derive the cyclic events, their finite inclusion--exclusion, and the
factorization over consecutive gaps in Appendix A, equations (A.3)--(A.6),
of *Statistics of persistent events in the binomial random walk: Will the
drunken sailor hit the sober man?* ([arXiv:cond-mat/9905252](https://arxiv.org/abs/cond-mat/9905252),
*Journal of Statistical Physics* 96 (1999), 963--1019,
DOI 10.1023/A:1004636216365). The paper presents the calculation for a
one-dimensional random walk. The Lean proof was checked against these exact
finite event identities; the broader state-space statement below is a
generalization inferred from the proof's hypotheses, not a claim attributed
to Bauer--Godrèche--Luck.

The repository's Mathlib dependency is pinned at
`380f2aafb622cb2c1c93dac545b6389083c68c51`. In that revision, the order
interface is expressed by `[AddCommGroup G] [LinearOrder G]
[IsOrderedAddMonoid G]`; the former bundled name `LinearOrderedAddCommGroup`
does not exist there. The relevant definitions are in the pinned
[Mathlib ordered-group source](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/Algebra/Order/Group/Defs.lean).
For measurability, the pinned
[Mathlib group-arithmetic source](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/MeasureTheory/Group/Arithmetic.lean)
provides `MeasurableAdd₂`. No cyclic-survival or cyclic-gap identity was
found in the corresponding Mathlib probability modules; the finite-sum and
coordinate-permutation ingredients are assembled from the existing algebra
and finite-product APIs.

The audit distinguishes the assumptions needed at each step. The finite
partial-sum identities use an additive commutative group. The cyclic cover
uses a minimum among finitely many partial sums, so its present proof uses a
linear order compatible with addition. The probability argument additionally
uses measurability of addition and an explicit hypothesis that
`Set.Ici (0 : G)` is measurable. Measurability of subtraction is not needed:
a rotated survival event is identified with the preimage of ordinary
survival under a coordinate permutation, which is measurable independently
of subtraction on `G`. This makes the published cyclic-gap theorem's
assumptions weaker than the first proof draft's assumptions.

The complete cyclic-gap expansion is a meaningful result in its own right,
so it is exposed as
`Probability/Process/RandomWalk/Fluctuation/SparreAndersen/Composition/CyclicGapSum.lean`.
Its statement covers i.i.d. increments valued in any linearly ordered
measurable additive commutative group satisfying the hypotheses above; the
real-valued positive-composition identity remains a specialization in
`Composition/Formula.lean`. Event descriptions and block-factorization
steps stay under `Composition/Lemmas/`, because their statements encode the
particular cyclic events and the assembly of this expansion. Their use by the
public theorem is not, by itself, a reason to externalize them.

## Abstraction research: finite consecutive-block product laws

The public declarations in
`Probability/Process/RandomWalk/Path/Block/Law/FiniteProduct.lean` package the
finite product law of an i.i.d. increment measure across consecutive blocks
of variable lengths. The exact statement allows each block to have its own
measurable event and identifies the joint event measure with the product of
the block event measures. Its hypotheses are an i.i.d. probability law and
measurability of those block events; no path regularity or moment assumption
is used.

The pinned Mathlib revision is
`380f2aafb622cb2c1c93dac545b6389083c68c51`. Its
[`Measure.pi_pi`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/MeasureTheory/Constructions/Pi.lean)
computes the measure of a measurable product rectangle for a finite product
of sigma-finite measures. The same file provides
`measurePreserving_piEquivPiSubtypeProd` for splitting coordinates into two
subfamilies and `measurePreserving_pi` for coordinatewise measure-preserving
maps. These are more general measure-theoretic primitives than the local
probability statement. The pinned source has no single theorem that packages
the ordered, variable-length consecutive-block event used here; the local
statement supplies that block-indexing adapter and obtains its law from
`iidSequenceLaw`.

A still broader theorem could allow a different sigma-finite measure at
each coordinate and express the block decomposition through a measurable
equivalence between `Fin n` and the dependent sum of the block index types.
That formulation is a finite-product measure decomposition, rather than a
random-walk probability result. The Mathlib coordinate-splitting and product
rectangle APIs already provide its general measure-theoretic ingredients;
adding another public wrapper solely to restate those APIs would duplicate
their abstraction. The current result therefore remains at the random-walk
block-law layer: it is a complete i.i.d. probability theorem with arbitrary
measurable block events, while its finite-coordinate geometry is supplied by
Mathlib. Its single current downstream use prompted this review but did not
determine its placement.

## Abstraction review: stable finite-variation entrance positivity (2026-10-19)

The finite-variation Poisson construction had been stored as
`Probability/Process/Stable/JumpModel/EntranceLaw.lean`, even though its
conclusion is positivity of the stable small-deviation event
`fullSegmentCorridorReturnEvent`. This made the reusable jump-model directory
depend on a small-deviation event. The result now lives at
`Stable/SmallDeviation/Blocks/Lower/Entrance/PoissonModel.lean`, and its public
theorem is
`IsStableLevyProcess.measure_fullEntrance_pos_indexLTOne`:

```lean
(h : IsStableLevyProcess α μ X P) → α < 1 →
(0 < cdf μ 0 ∧ cdf μ 0 < 1) → -1 < b ∧ b < 1 → -1 < c ∧ c < 1 →
0 < ε → 0 < P (fullSegmentCorridorReturnEvent X 0 1
  (c - 1) (c + 1) (c - b - ε) (c - b + ε))
```

The proof-only statement with an explicit
`LevyKhintchineTriple`, `SigmaFinite` instance, and characteristic-function
identity is now a private lemma in that module. Strict stability already
provides such a triple, so including it in the public theorem's assumptions
would expose a proof representation rather than the mathematical condition.
The narrower half-open endpoint wrapper and four scaled/log-ratio wrappers
in `ShiftComparison/PoissonEntrance.lean` had no callers beyond their own
adapter chain; the scaled form is already supplied by the stable scaling API,
and the other wrappers were removed with that unused chain. The all-index
entrance statement remains the only entry in `ShiftComparison/AllIndices.lean`.

The abstraction review compared three levels. First, the pinned Mathlib
revision is `380f2aafb622cb2c1c93dac545b6389083c68c51`; its
[`map_eq_iff_forall_finset_map_restrict_eq`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/Probability/Process/FiniteDimensionalLaws.lean)
states that equality of all finite-dimensional distributions is equivalent
to equality of process laws for almost-everywhere measurable process maps
under a finite measure. Second, the repository's
`HasIndepIncrements.process_identDistrib_of_aemeasurable` is a cross-space
process-law theorem: zero starts, independent increments, and matching
increment distributions imply equality of the process laws. These are the
general law-transfer ingredients used by the Poisson proof; they already live
at their general process-law layer.

Third, the repository's path-space support theorem accepts an arbitrary
probability measure on `CadlagPath unitInterval ℝ`: if the straight path to
`c-b` belongs to its support, then the corresponding open corridor and
terminal window have positive joint probability. This is more abstract than
the stable adapter, and remains in the path/support layer. Thomas Simon's
“Petites déviations et support d'un processus de Lévy,” *Comptes Rendus de
l'Académie des Sciences*, Série I 329(4) (1999), 331--334, DOI
[10.1016/S0764-4442(00)88576-6](https://doi.org/10.1016/S0764-4442(00)88576-6),
and its expanded treatment “On the small deviations of a Lévy process,”
*Potential Analysis* 14 (2001), 155--173, DOI
[10.1023/A:1008711917156](https://doi.org/10.1023/A:1008711917156), characterize
small-deviation support and the support of Lévy laws in Skorokhod space. This
is a possible route to a broader Lévy-process support interface, but it does
not by itself identify the present prescribed nonzero terminal window from
the CDF sign condition. The finite-variation construction supplies that
specific implication. Therefore the general law-transfer and path-support
results stay public at their existing abstract layers, while the stable
entrance theorem stays with its small-deviation event. Cross-module use was
only the audit trigger; the placement follows these mathematical interfaces.

## Abstraction review: uniform-block feedback probabilities (2026-10-19)

The former `Stable/SmallDeviation/Blocks/Factorization.lean` contained two
theorems whose proofs used only independent increments, stationary increments,
coordinate measurability, and the rational uniform-block event interface.
Neither conclusion used a stable law. The finite product lower bound now lives
in `Probability/Process/Path/Skorokhod/Corridor/UniformBlocks/Probability.lean`
as
`HasIndepIncrements.pow_le_measure_rationalUniformPrefixBlockEvent`:

```lean
(h : HasIndepIncrements X P) → HasStationaryIncrements X P →
(∀ t, AEMeasurable (fun ω => X t ω) P) → MeasurableSet V →
q ≤ P (block 0 ∈ V) →
q ^ blocks ≤ P (every translated uniform block lies in V)
```

This is the weakest process interface used by the formal proof; it does not
assume zero start, càdlàg paths, stability, a moment condition, or a scaling
law. The stable finite-time entrance argument supplies its process facts and
one-block estimate at the application boundary.

The abstraction comparison checked pinned Mathlib revision
`380f2aafb622cb2c1c93dac545b6389083c68c51`. Its
[`iIndepFun.measure_inter_preimage_eq_mul`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/Probability/Independence/Basic.lean)
is stronger at the measure-theoretic level: for an arbitrary finite family of
independent random variables and measurable coordinate events, it gives the
exact finite-product identity, including a different event for each index.
The repository's
`HasIndepIncrements.iIndepFun_rationalUniformBlocks` and
`HasIndepIncrements.rationalUniformBlockProcess_identDistrib` provide the
path-process independence and stationarity specializations. The new theorem
packages these process facts into the complete lower bound for the existing
uniform-prefix event. Its common event `V` matches that event's meaning; for
different measurable events at each block, the general Mathlib product
identity is the more abstract endpoint and requires no additional local
wrapper.

The other former declaration,
`IsStableLevyProcess.measure_prefixTube_inter_nextBlock`, was a single-use
stable receiver around
`HasIndepIncrements.indepFun_rationalPrefix_nextBlock` followed by
`IndepFun.measure_inter_preimage_eq_mul`. It was removed; the upper-bound
proof now applies those general APIs directly. Thus the former
`Blocks/Factorization.lean` file was deleted rather than retaining a
stable-specific public facade. The repository's generic
`measure_adaptiveChoice_ge_mul` likewise already states the binary feedback
inequality for arbitrary independent past and future maps; the path-level
feedback module applies it to rational block paths, and its public interface
now assumes only independent increments and coordinate measurability.

## Abstraction review: finite-choice block feedback (2026-10-19)

`Stable/SmallDeviation/Blocks/Lower/Binning/Basic.lean` also contained the
one-step estimate `IsStableLevyProcess.measure_prefixBin_nextBlock_ge_mul`.
Its proof used only the finite-partition measure inequality,
`HasIndepIncrements.indepFun_rationalPrefix_nextBlock`, and coordinate
measurability. The stable-law assumption supplied only the last item. The
three lower-block consumers in `Return/Basic.lean` and
`Assembly/Concatenation.lean` now call
`HasIndepIncrements.measure_rationalPrefixFiniteChoiceNextBlock_ge_mul` in the
uniform-block feedback module. Its hypotheses are independent increments,
almost-everywhere measurable coordinates, measurable prefix and next-block
events, pairwise disjoint prefix cells, and a common lower bound for each
cell's next-block event. Its conclusion is the full finite-choice inequality
for rational uniform-block paths; no stationary or stable increment law is
needed. The tube-covering specialization remains in the stable small-deviation
layer because it additionally uses the stable application’s endpoint bins
and coverage statement.

The comparison used pinned Mathlib revision
`380f2aafb622cb2c1c93dac545b6389083c68c51`. Mathlib's
[`IndepFun.measure_inter_preimage_eq_mul`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/Probability/Independence/Basic.lean)
is the general factorization theorem for two independent random variables
and measurable coordinate events. The repository's
`MeasureTheory.measure_iUnion_inter_ge_mul_of_finite_partition` already
states the measure inequality for arbitrary finite disjoint families, without
assuming independence. Their combination now gives the separate public
`measure_finiteAdaptiveChoice_ge_mul` in `Probability/Independence/Feedback.lean`:
for arbitrary measurable past and future spaces, an independent pair of random
variables, a finite disjoint family of past events, and one future event per
cell, the lower bound follows from a common lower bound on the selected future
probabilities. This is a finite-choice theorem with independent use beyond
the path application, and it strictly generalizes the existing binary
feedback principle. The path-level result then applies it to uniform
prefix/next-block maps using `HasIndepIncrements`; it retains the richer
process statement without adding a stable-law assumption. The
[`Mathlib independence documentation`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html)
and [`independent-increments documentation`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Process/HasIndepIncrements/Basic.html)
confirm the semantics and scope of those interfaces.

## Abstraction review: stable uniform-block upper bound (2026-10-19)

`Stable/SmallDeviation/Blocks/Upper/Basic.lean` had an unused public theorem
`IsStableLevyProcess.measure_rationalPrefixTube_eq_prod`; a repository-wide
source search found no callers. Its proof recursively factored each prefix
tube event from the next block using
`HasIndepIncrements.indepFun_rationalPrefix_nextBlock` and
`IndepFun.measure_inter_preimage_eq_mul`. The pinned Mathlib API provides the
more general finite-family product formula
[`iIndepFun.measure_inter_preimage_eq_mul`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/Probability/Independence/Basic.lean);
the repository already derives mutual independence of the rational block
paths and exposes the exact tube-event product in
`Probability/Process/Path/Skorokhod/Corridor/UniformBlocks/Probability.lean`.
The unused stable-specific recurrence was therefore removed rather than
promoted as another wrapper. The complete stable-process power bound and the
rational form of Mogulskii's equation (23) remain in `Upper/Basic.lean`, where
their process law and scaling assumptions belong.

## Abstraction review: positive-`a` endpoint PZ chain (2026-10-19)

The proof family had been grouped in a directory named after its parameter
condition rather than the mathematics in the files. It now lives under
`EndpointDeviation/FirstStage/`: the entry proves an
exponential low-count bound for the first-stage killed population, and its
PZ-specific rate assembly is grouped under `Lemmas/`. The `rightTailPositiveA`
identifier remains in theorem names because those statements are indexed by
the positive exponent parameter; it no longer determines directory placement.

`EndpointDeviation/FirstStage/Lemmas/PZBudget.lean` estimates the
tilted-spine corridor mass at the specific cutoff
`rightTailPositiveAFirstCutoff`; its only client is `PZAssembly.lean`.
`PZAssembly.lean` combines that rate with the first-stage MRCA pair sum and
cross-child weight. Its resulting PZ-mean lower bound is used by both
`FirstStage/LowCountPower.lean` and
`SecondStage/Roots/CountBudget.lean`, which allocates the first-stage bound to
the second-stage root budget. Neither statement is the general
Paley--Zygmund inequality: both contain the selected population's tilted law,
corridor, cutoff, and model-specific pair bound. They therefore remain
theorem-family lemmas under `FirstStage/Lemmas/`; the second-stage use is a
consumer of the first-stage estimate, not a more general mathematical
interface.

The deterministic schedule and its scale properties now live beside their
owner in `Drawdown/Spine/Cutoff.lean`. The limit
`logarithmicSmallDeviationScale (rightTailPositiveAFirstCutoff N n) /
logarithmOfSampleSize N n → 1` had been proved independently in
`PZBudget.lean` and `Spine/Corridor.lean`. It is now one named property of the
cutoff used by both stages; it remains at the endpoint-deviation subject level
because it describes this model-specific schedule rather than a general
asymptotic operation.

The pinned Mathlib source at revision
`380f2aafb622cb2c1c93dac545b6389083c68c51` has no declaration named for the
Paley--Zygmund inequality. Its general probability-space form had already
been proved in `BranchingProcess/GaltonWatson/Growth.lean`; its location and
namespace were narrower than its assumptions and conclusion. It is now exposed
from `Probability/MeasureTheory/Moments/PaleyZygmund.lean` as
`ProbabilityTheory.measure_ge_threshold_of_moments`: for `X ≥ 0` almost
everywhere, `X ∈ L¹ ∩ L²`, `𝔼[X] = m`, `𝔼[X²] = s > 0`, and `0 ≤ t < m`,
`(m - t)² / s ≤ ℙ(t ≤ X)`. This is the random-variable form of Paley and
Zygmund, [*On some series of functions, (3)*, Lemma 19, p. 192
(1932)](https://doi.org/10.1017/S0305004100010860). The module also contains
the general corollary `measure_ge_threshold_of_secondMoment_le`. The Galton--Watson moment
recurrences and finite-generation specializations remain in `Growth.lean`.

The API review compared this statement with Mathlib's general
[Markov inequality](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean)
and [(L^2) integral API](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/MeasureTheory/Function/L2Space.lean).
These supply neighboring ingredients, while the pinned revision has no
Paley--Zygmund theorem; the general probability-space statement is the useful
public abstraction, and the model-specific rate lemmas remain under
`FirstStage/Lemmas/`. Their use in later modules alone does not justify
promoting them. These support files retain the legacy header for now:
`Population/PZInput.lean`, which defines their theorem-level data, also uses the
legacy import form, and Lean rejects importing it from an isolated
module-system file. Migrate this dependency closure together in the
repository-wide module-system pass.

## Abstraction review: root-indexed Ulam--Harris families (2026-10-19)

The root-indexed tree types in `Combinatorics/UlamHarris/Tree/Defs.lean` and
`MarkedTree/Basic.lean` are aliases for function families:
`RootIndexed.Tree Root α = Root → Tree α` and
`RootIndexed.MarkedTree Root α X = Root → MarkedTree α X`. The first module
also defined a `reindex` operation by `T.reindex f := fun r => T (f r)` and
proved its application, identity, and composition equations. The marked-tree
module repeated the same operation and laws; the only client of that wrapper
was its local mark-forgetting equation.

We compared these candidate APIs with the pinned Mathlib revision
`380f2aafb622cb2c1c93dac545b6389083c68c51`. `Function.comp` already states
precomposition at arbitrary function types, with `Function.comp_apply`,
`Function.comp_assoc`, `id_comp`, and `comp_id`; see Mathlib's
[`Logic/Function/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/Logic/Function/Basic.lean)
and [`Logic/Function/Defs.lean`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/Logic/Function/Defs.lean),
and the [official function API documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Function/Defs.html).
The indexed-tree `reindex` declarations added no structure or theorem beyond
that function API and had no independent clients, so they were removed.
Pointwise root, parent, and sibling wrappers were removed for the same reason:
each is obtained directly from the corresponding field of `T r`. The
`FiniteRootTree` and `CountableRootTree` aliases and the finite extensionality
alias had no clients and introduced no additional structure. The single-tree
`Tree.mem_parent` remains because the graph arborescence proof uses its
parent-prefix formulation; `Tree.ext` remains used by the marked-tree and
branching-walk equivalence proofs.

The root-indexed mark-forgetting equation is retained in the more direct form
`forgetMark (M ∘ f) = forgetMark M ∘ f`, as
`RootIndexed.MarkedTree.forgetMark_comp`. This records the naturality of the
semantic projection without defining a tree-specific composition operation.

The related `ProbabilityTheory.BranchingRandomWalk.RootIndexed.StepField`
API was checked against the generic function interfaces in the pinned Mathlib
revision `380f2aafb622cb2c1c93dac545b6389083c68c51` and the Lean 4.35.0-rc3
core API, following the cross-module abstraction review rule in
[`CONTRIBUTING.md`](../../CONTRIBUTING.md#lean-module-headers-and-mathematical-references).
For
`step : Root → TreeNode α → Step α X` and
`f : NewRoot × TreeNode α → Root × TreeNode α`, the most general ordinary
function expression for the coordinate pullback is
`Function.curry (Function.uncurry step ∘ f)`. Mathlib's
[`Function.bicompl`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/Logic/Function/Defs.lean)
is another candidate, with
`Function.uncurry (Function.bicompl step g h) =
Function.uncurry step ∘ Prod.map g h`; it covers separately reindexed
coordinates but not an arbitrary joint map `f`, where the selected root may
depend on the address. The general candidate is therefore composition after
uncurrying, followed by currying, using Lean's
[`Function.curry` and `Function.uncurry`](https://leanprover-community.github.io/mathlib4_docs/Init/Data/Function.html)
and Mathlib's
[`Function.comp`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Function/Defs.html).
These interfaces require no probabilistic, finiteness, or injectivity
assumptions.

The subject-level
`RootIndexed.StepField.reindexCoordinates` remains a named semantic operation
in `Probability/BranchingRandomWalk/Genealogy/RootIndexed/Field/Basic.lean`:
it returns a root-indexed branching step field from an arbitrary map of its
root/address coordinates, and the probability-law and selected-coordinate
interfaces use that field-valued map. Its 50 references across eight modules
confirm those call sites; the count is not the reason to promote it to a more
general layer. The coordinate operation already accepts the weakest natural
assumptions, while a new general pullback declaration would repeat
`Function.comp` together with currying. Accordingly, the unused
`reindexCoordinates_id` and `reindexCoordinates_comp` wrappers were removed;
their content is supplied by the general composition and currying laws. The
root-only `reindex` remains the named specialization for relabelling initial
ancestors and is connected to coordinate pullback by
`reindex_eq_reindexCoordinates`.

## Abstraction review: countable-range coordinate evaluation (2026-10-19)

The dynamic coordinate measurability proofs in
`Probability/BranchingRandomWalk/Tree/Filtration.lean` and
`Probability/BranchingRandomWalk/Genealogy/RootIndexed/Field/Filtration.lean`
had the same measurable-union argument. The pinned Mathlib revision
`380f2aafb622cb2c1c93dac545b6389083c68c51` provides
[`Measurable.eval`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean#L591)
for one fixed coordinate and
[`Measurable.of_eval`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean#L596)
for a function into a full `Pi` space, whose hypothesis gives measurability
at every coordinate. The [official API documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Constructions.html)
states these same interfaces. Neither covers evaluation at a selector whose
actual range is countable while the ambient index type can be uncountable.

The general useful statement is placed in
`MeasureTheory/MeasurableSpace/CountableEvaluation.lean`:

```text
F : Ω → I → X,  s : Ω → I,
Countable (range s),
∀ i ∈ range s,  Measurable (fun ω => F ω i),
∀ i ∈ range s,  MeasurableSet {ω | s ω = i}
⊢ Measurable (fun ω => F ω (s ω)).
```

The index type `I` has no measurable-space assumption, and the two
measurability hypotheses are required only for indices that can actually be
selected. This is weaker and more reusable than either branching-specific
theorem. The public `Measurable.eval_of_countable_range` proves it by
expressing each preimage as a countable union of the selector fiber
intersected with one coordinate preimage. The two filtration theorems now
specialize this result using their respective depth conditions and measurable
selector fibers. The general theorem belongs in the public measurable-space
layer; the two filtration statements remain public at their semantic owners.
No branching-specific wrapper was moved outward based on its client count.

## Abstraction review: graded-coordinate filtrations (2026-10-19)

The tree-mark filtration and the root-indexed step-field filtration both
reveal a coordinate according to the depth of its address. Their common
mathematical structure is a family of observations `X_i : Ω → E_i` with a
revelation grade `r(i)` in a time preorder:

`𝓕_t = ⨆_{i : I} ⨆_{r(i) ≤ t} MeasurableSpace.comap X_i m_{E_i}`.

The pinned Mathlib revision
`380f2aafb622cb2c1c93dac545b6389083c68c51` was checked against three nearby
interfaces. `MeasureTheory.Filtration.natural` uses the same index as both the
observation index and time, and assumes strongly measurable maps into
metrizable Borel spaces. `MeasureTheory.Filtration.piLE` is the canonical
filtration on a product indexed by a preorder, with the coordinate order
itself determining revelation time. `MeasureTheory.filtrationOfSet` generates
a filtration from one event per time. The first two are documented in the
[official Filtration API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/Filtration.html);
their pinned definitions are in
[`Filtration.lean`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/Probability/Process/Filtration.lean#L395)
(`natural`),
[`Filtration.lean`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/Probability/Process/Filtration.lean#L494)
(`piLE`), and
[`Filtration.lean`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/Probability/Process/Filtration.lean#L230)
(`filtrationOfSet`). None directly gives a family indexed by an arbitrary
`I` whose grades are mapped into an arbitrary time preorder, while retaining
only measurable-space assumptions on the possibly dependent `E_i`.

The coordinate form also preserves the former generator-set presentation:
Mathlib's `MeasurableSpace.comap_eq_generateFrom` identifies each coordinate
comap with the σ-algebra generated by its measurable preimages, and
`MeasurableSpace.generateFrom_iUnion_measurableSet` identifies their supremum
with the σ-algebra generated by the union of those preimages. These identities
are available in the pinned
[`MeasurableSpace.Basic`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/MeasureTheory/MeasurableSpace/Basic.lean#L95)
and
[`MeasurableSpace.Defs`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/MeasureTheory/MeasurableSpace/Defs.lean#L480)
interfaces.

The resulting reusable API is placed at
`Probability/Process/Filtration/GeneratedByCoordinates.lean`:

* `MeasureTheory.Filtration.generatedByCoordinates` constructs the filtration
  with the displayed formula from any measurable coordinate family with
  possibly dependent codomains and grade map `r : I → T`.
* `MeasureTheory.Filtration.measurable_coordinate_generatedByCoordinates`
  proves that each coordinate is measurable once `r(i) ≤ t`.
* `MeasureTheory.Filtration.generatedByCoordinates_le` characterizes it as
  the least filtration with those coordinate measurability properties.
* `MeasureTheory.Filtration.measurable_to_generatedByCoordinates` proves the
  sufficient direction, and
  `MeasureTheory.Filtration.measurable_iff_coordinates_generatedByCoordinates`
  records the full iff: coordinatewise measurability is necessary by the
  generator maps and sufficient by the universal property of the generated
  σ-algebra.

This abstraction states the shared filtered-information structure and its
minimality, rather than merely deduplicating two `generateFrom` proofs. In the
branching specializations, the grade is `u.length + 1`, so
`u.length < n` is exactly the condition that the coordinate is visible at
generation `n`. The subject modules keep their named `generationFiltration`
and `stepFiltration` interfaces and use the generic API for their measurable
coordinate proofs and root restriction/reindexing maps.

## Abstraction review: conditional event iteration (2026-10-19)

`Probability/Process/Filtration/ConditionalBlocks.lean` is used by the
drawdown, horizontal-tube, and drifted-tube arguments. Its public iteration
theorems concern arbitrary measurable event sequences and filtrations; the
random-walk block events are supplied by callers. This is a complete
conditional-probability estimate at the process-probability layer, rather
than a proof step tied to any one small-deviation argument.

Mathlib's pinned
[`setIntegral_condExp`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean#L231)
and its [official conditional-expectation API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.html)
give the integral identity for a general integrable function and a
sub-σ-algebra. They do not provide the finite sequence event intersection or
the resulting product bound. The local one-step event inequality turns that
identity into an intersection-mass bound; the public product theorems then
iterate it under a filtration and conditional indicator bounds.

The probability-measure assumption matches the unscaled product conclusions:
`conditionalBlockIntersection events 0 = Set.univ`, so the induction base
uses `P.real Set.univ = 1`. A finite measure without normalization would need
the factor `P.real Set.univ` on the product side. The abstraction review
therefore keeps the current probability statement and its natural hypotheses;
dropping `IsProbabilityMeasure` alone would make the displayed bounds false.
The theorem already leaves the state space, events, filtration, and numeric
bounds arbitrary, so no random-walk-specific wrapper is promoted to this
layer.

## Abstraction review: finite product reindexing (2026-10-19)

`Probability/Sequence/IID/FiniteReindex.lean` supplies the coordinate
permutation name used by the cyclic-path argument and a finite-cover estimate
for repeated-coordinate product measures. The former makes the path action
readable at its use site: it is the homogeneous `Fin n` specialization of
Mathlib's `MeasurableEquiv.piCongrLeft`, oriented so that coordinate `i` of
the reindexed vector is the original coordinate `e i`. The latter adds the
event-cover bound needed by the random-walk entrance argument.

The pinned Mathlib revision already has the more general dependent-coordinate
result `Measure.pi_map_piCongrLeft`: it maps a product of a σ-finite family
of measures along a reindexing equivalence to the reindexed product. Its
[official API documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/Pi.html)
and pinned source
[`Constructions/Pi.lean`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/MeasureTheory/Constructions/Pi.lean#L745)
show that neither identical marginals nor probability normalization are
required for product reindexing. The local set-preimage equality merely
rewrapped that theorem and had no clients outside its defining module, so it
is now private. The public finite-cover result uses the weaker natural
assumption `[SigmaFinite ν]`; this is sufficient both for Mathlib's product
reindexing theorem and for the measure inequality, which does not depend on
normalization. The generic finite-cover step itself remains in
`MeasureTheory/OuterMeasure/Finite/Cover.lean`.

## Abstraction review: finite-cover outer-measure bounds (2026-10-19)

The cross-module cover arguments were compared with the pinned Mathlib API at
revision `380f2aafb622cb2c1c93dac545b6389083c68c51`. Mathlib's
[`OuterMeasure.Basic` API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/OuterMeasure/Basic.html)
defines an outer measure on `Set Ω → ℝ≥0∞` without a measurable-space
structure, and provides `measure_mono` and
`measure_biUnion_finset_le` for any `OuterMeasureClass`. The two finite-cover
statements therefore use the weaker semantic structure directly:

- If `event ⊆ ⋃ k ∈ cover, rotate k ⁻¹' safe` and each such preimage has the
  same outer measure as `safe`, then
  `μ event ≤ cover.card • μ safe`.
- If `U ⊆ ⋃ i ∈ F, A i`, every cell has a subset `A i ∩ B i ⊆ T`, and
  `c * μ (A i) ≤ μ (A i ∩ B i)`, then
  `c * μ U ≤ F.card * μ T`.

These are generic finite-cover operations, rather than probability-specific
results: neither requires measurable sets, a probability normalization, nor a
particular finite index type. The first statement supports the cyclic-cover
argument in `Probability/Sequence/IID/FiniteReindex.lean`; the second supports
the corridor comparison in `Probability/Process/RandomWalk/Path/Block/Corridor/Comparison.lean`.
The finite subadditivity step is already Mathlib's
`measure_biUnion_finset_le`, so this module adds only the useful finite-cover
consequences and does not duplicate the underlying outer-measure API. The
statements live at `MeasureTheory/OuterMeasure/Finite/Cover.lean`, their
semantic owner, instead of the former probability-measure-oriented
`MeasureTheory/Measure/Finite/Cover.lean` path.

The API comparison is documented in the official documentation above; its
source is pinned at
[`OuterMeasure/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/MeasureTheory/OuterMeasure/Basic.lean#L80).

## Same-basename module and directory review (2026-10-19)

The first-party Lean source tree has no sibling pairs of the form `Foo.lean`
and `Foo/`, and no direct child file repeats its parent directory in its
basename. The test modules formerly named `TruncationMoments`,
`TruncationSecondMoment`, `BranchingWalkLaw`, `RandomWalkPathLaw`, and
`EndpointDeviationParameters` now use names relative to their directories.
The pinned Mathlib source does use same-basename pairs intentionally; the
`Mathlib.MeasureTheory.Measure.Dirac` entry module re-exports
`Dirac.Def` and `Dirac.Basic`, as shown in the
[official module documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Dirac.html).
The repository keeps its stricter rule from `CONTRIBUTING.md`: substantive
core declarations live in a file such as `Basic.lean`, while a subject
directory owns its semantically grouped modules. This keeps an import path
from appearing both as a file and as a directory in the project API. The
Mathlib pattern is an intentional umbrella-module design, not a reason to
mechanically rename local modules or a basis for claiming that Mathlib has no
such pairs.

## Abstraction review: convergence interfaces (2026-10-19)

The review started with the probability-measure convergence wrappers and
also checked the existing weak-convergence independence interface. Cross-module
use was treated as a reason to search for the mathematical abstraction, rather
than as the placement criterion.

`Measure.map_eq_of_ae_pointwise_limit` concerns a finite Borel measure and
measurable self-maps; it does not use probability normalization or random
variables. Its owner is therefore `MeasureTheory/Measure/Convergence`, and the
module now lives at `MeasureTheory/Measure/Convergence/MapInvariance.lean`.
The pinned Mathlib API has no direct closure theorem for invariant measures
under almost-everywhere pointwise limits. Its
[`HasOuterApproxClosed` API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.html)
provides uniqueness of finite Borel measures from bounded continuous test
functions, while dominated convergence provides convergence of their
integrals. The local theorem combines those general ingredients to prove the
invariance conclusion. This comparison was checked against Mathlib revision
`380f2aafb622cb2c1c93dac545b6389083c68c51`, including
[`HasOuterApproxClosed.lean`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean)
and the official documentation above.

The weak-convergence review found that
`Probability/ConvergenceInDistribution/Independence.lean` already contains the
forward direction: independent coordinates with convergent marginal laws give
joint convergence to independent limits. The converse closure theorem,
`ProbabilityTheory.indepFun_of_tendstoInDistribution_pair`, now lives beside
it. It allows source spaces and laws to vary with the index, assumes each pair
has independent coordinates, and concludes independence of the limit from
joint-law convergence. The two directions form one coherent finite-product
interface; this placement follows the mathematical subject, not the number of
clients. The proof uses continuity of `ProbabilityMeasure.prod` and Mathlib's
characterization of independence by equality of the joint law with the product
law. The pinned APIs are
[`MeasureTheory.TendstoInDistribution.continuous_comp`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/ConvergenceInDistribution.html),
[`ProbabilityMeasure.continuous_prod`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.html),
and
[`indepFun_iff_map_prod_eq_prod_map_map`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html).
Mathlib's `tendstoInDistribution_of_ae_tendsto` supplies the joint-law
convergence in the Brownian first-passage application. This audit used the
online Mathlib documentation and pinned source at revision
`380f2aafb622cb2c1c93dac545b6389083c68c51`.

The former `ProbabilityTheory.tendsto_integral_of_eLpNorm_one_sub_const` was
removed because no module used it and Mathlib already proves the stronger
`MeasureTheory.tendsto_integral_of_L1'`: convergence in `L¹` to an arbitrary
integrable function implies convergence of its Bochner integrals, for general
measures and complete normed codomains. The local probability/real/constant
statement was only a specialization. See the pinned
[`Bochner.Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean)
and its [official documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner/Basic.html).

### Polynomial tails and logarithmic fourth moments

`L2FromPolynomialTails.lean` now states the moment-growth exponent as an
arbitrary real `q`: if the fourth moments are eventually bounded by
`C * (1 + (log n)^q)` and each fixed two-sided tail is bounded by a possibly
different polynomial rate, then the second moments tend to zero. The previous
fixed exponent `8` reflected one application rather than the mathematical
criterion, so the API now exposes the full real-exponent form.

The closest broader Mathlib theorem is the Vitali criterion
`MeasureTheory.tendstoInMeasure_iff_tendsto_Lp_finite`: for a finite measure
and `1 ≤ p < ∞`, convergence in measure together with uniform integrability
is equivalent to convergence in `Lᵖ`. It is more abstract, but it takes
uniform integrability and convergence in measure as inputs rather than the
explicit polynomial-tail and fourth-moment hypotheses used here. The project
therefore keeps the checkable tail-to-`L²` criterion, with its final step
factored through the more general local interface
`ProbabilityTheory.tendsto_integral_sq_of_tendsto_fourthTailControl` in
`L2FromTails.lean`.

The real exponent is supported by Mathlib's
`isLittleO_log_rpow_rpow_atTop`, which proves
`(log x)^q = o(x^p)` for every real `q` and every `p > 0`. This was checked in
the pinned Mathlib revision `380f2aafb622cb2c1c93dac545b6389083c68c51`,
[`Analysis/SpecialFunctions/Pow/Asymptotics.lean`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L365), and against the official
[API documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.html). The Vitali comparison uses the pinned
[`MeasureTheory/Function/UniformIntegrable.lean`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/MeasureTheory/Function/UniformIntegrable.lean#L566)
and its [official documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/UniformIntegrable.html).

## Abstraction review: unit-second-moment Gaussian attraction (2026-10-19)

`Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/CLT.lean`
packaged the central limit theorem as a centered unit-second-moment Gaussian
domain-of-attraction result. Its statement has no Mogulskii scale, corridor,
or path-space premise, so it belongs to the distributional normal-attraction
API. `Probability/Distributions/Stable/Attraction/Normal/Basic.lean` already
proves the stronger finite-positive-second-moment result with normalization
`sqrt (n * ∫ x² dν)`. The unit-second-moment corollary now lives beside that
general theorem; `integrable_of_integral_eq_one` derives square integrability
from the moment identity, and the normalization simplifies to `sqrt n`.

The Mogulskii-local CLT module was removed. Its existential normal-attraction
wrapper duplicated the `Along` theorem's existing `.isInDomainOfAttraction`
projection, and its strictly `2`-stable wrapper duplicated the general
finite-variance theorem in the same normal-attraction module. Brownian path
limit and Gaussian small-deviation clients now import the distributional
theorem directly. The unit-second-moment corollary is public because it is a
complete distributional result that applies beyond Mogulskii; it is not a
proof-only `Lemmas/` artifact.

## Structural sweep (2026-10-19)

A path audit of the 1,465 production Lean modules under the eight library
roots, excluding `Vendor/` and `BranchingProcessTest/`, found no directory with
more than eight direct `.lean` files, no same-level `Foo.lean`/`Foo/` name
collision, and no path named `Source` or `source`. The tree has 23 `Lemmas/`
directories; none has a parallel `Lemmas.lean` at the same level, and no
production module outside a `Lemmas/` directory uses `public import` for a
module inside one. These checks enforce discoverability and proof-import
boundaries; they do not replace the declaration-by-declaration abstraction
review documented above.

`python3 scripts/run-mathlib-lint-style.py` completed successfully on all
1,465 modules. Mathlib's linter driver emitted its own missing-`module`
header warning for `scripts/lint-style.lean`; it did not report a style issue
in the production modules. The full `lake build BranchingProcess` also
completed successfully (5,576 jobs). It reports a non-fatal module-system
advisory in `Selection/NSelection/EndpointDeviation/FirstStage/Lemmas/PZBudget.lean`:
that legacy module imports the modern Mathlib asymptotics module, while two of
its project dependencies are legacy modules. Adding a `module` header to this
file alone makes Lean reject those dependencies; a fix requires migrating the
whole import chain together.

The separate `BranchingProcessTest/` tree contains 138 Lean modules and was
checked independently: it has no directory with more than eight direct test
modules, no same-level file/directory name collision, no `Source`-named
directory, and no parallel `Lemmas.lean`/`Lemmas/` entry.

## Stable norming ownership and Mogulskii module headers (2026-10-19)

`Mogulskii/Stable/TruncatedMoment.lean` used only a probability measure,
truncated moments, and the distributional norming factor $L^*$; its theorem
statements had no walk, path, or small-deviation hypotheses. It therefore
belongs with the stable norming definition rather than under the random-walk
small-deviation development. The module now lives at
`Probability/Distributions/Stable/Attraction/Norming/TruncatedMoment.lean`,
beside the tail and norming results, and the stable-attraction test imports
that owner. The fully general truncated-moment identities remain in
`Probability/Distributions/Moments/Truncated/Basic.lean`; the moved results
are the stable-factor specializations $L^*(u)\to A-B$ and
$L^*(u)\to\alpha B/(2-\alpha)$ under their respective tail limits.

The identity `IsStableLevyProcess.unitIntervalPathLaw_spatialScale` was also
inside `TerminalLeft/Normalization.lean`. Its proof only needed an
almost-surely càdlàg real process, so that stable-process wrapper was removed
and the reusable theorem `pathLaw_smul` was added to
`Probability/Process/Path/Cadlag/MeasurableMap.lean`. It states
`pathLaw(P, qX) = (pathLaw(P, X)).map (scalePath q)` for every real `q`.
`PathLaw/UnitInterval.lean` now owns only the stable-process path-law
construction and stable-clock results. The one-use coefficient substitution
`sourceNormalization` is private in the terminal-left normalization module;
the exported raw-normalization theorem remains there.

The public abstraction reviewed for this move is: for any real process
`X : unitInterval → Ω → ℝ` with `AEMeasurable (X t) P` at every time and
almost-surely càdlàg paths, and any `q : ℝ`,
`pathLaw(P, qX) = (pathLaw(P, X)).map (scalePath q)`. No probability,
independent-increment, stable-law, or positivity assumption on `q` is needed.
The pinned Mathlib source at revision
[`380f2aafb622cb2c1c93dac545b6389083c68c51`](https://github.com/leanprover-community/mathlib4/tree/380f2aafb622cb2c1c93dac545b6389083c68c51)
provides the generic map steps used in the proof:
[`Measure.map_congr`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/MeasureTheory/Measure/Map.lean#L130)
and
[`AEMeasurable.map_map_of_aemeasurable`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/MeasureTheory/Measure/AEMeasurable.lean#L160).
Mathlib supplies these measure-map operations but has no `CadlagPath` path-law
API; the reusable path-law statement therefore belongs in the project's
`Probability/Process/Path/Cadlag/MeasurableMap.lean`.

The module headers in `Stable/Scale/Rate.lean`,
`Stable/RandomWalkBounds/Partition/{EnergyUpper,Upper}.lean`, and
`Stable/RandomWalkBounds/PathClass/InnerOuter.lean` now list their exact public
declarations and quantitative conclusions. These are candidate-list fixes
from the lexical header scan, followed by inspection of each declaration and
its assumptions; the scan itself is not treated as proof that the full
Mogulskii tree has been audited. The moved module and the affected production
entry modules build with the pinned toolchain; the stable-attraction check
module also compiles through `lake env lean` against the new import path.
`Stable/Corridor.lean` and the equation (34) CDF entrance adapter now also
list their complete public APIs and quantitative conclusions. The
`Process/Path/Cadlag/MeasurableMap`, `PathLaw/UnitInterval`, and the
terminal-left normalization client build after adding the general path-law
scaling theorem and making the local coefficient substitution private.
`python3
scripts/check-lean-import-boundaries.py` also passes after these moves (10
public entries, 818 graph visits).

## Abstraction review: Rademacher normal-constant chain (2026-10-19)

`Stable/RandomWalkBounds/NormalConstant.lean` used to expose the constant
corridor, its one-piece finite-corridor representation, the constant
approximation, its energy limits, and path-event equivalences. Source search
found that these declarations serve only the rate-transfer proof in the same
file, so they are now `private`. The remaining rate-transfer lemma moved to
the Gaussian escape-constant proof family below.
The Rademacher identity
`truncatedSecondMoment rademacherMeasure u = 1` for `1 ≤ u` depends only on
the distribution and the generic truncated-moment definition; it now lives
in `Probability/Distributions/Rademacher.lean` beside the Rademacher law.

The rate-transfer lemma was also a single proof-chain dependency of the
Gaussian escape-constant theorem. It now lives at
`Gaussian/Lemmas/NormalConstant.lean`, under the Gaussian namespace; the
entry point imports it ordinarily. This places the non-reusable bridge in the
theorem's proof family without publishing it from `Gaussian/EscapeConstant`.
The scale identity
`stableSmallDeviationRate 2 rademacherMeasure scale =ᶠ[atTop] fun n =>
scale n ^ 2 / n` has one client in the proof of the Gaussian escape constant,
so it is now a private lemma in `Gaussian/EscapeConstant.lean`. The entry's
public imports name the direct owners of `IsBrownianReal`, `IsMogulskiiScale`,
`IsStableLevyProcess`, `pathLaw`, and `HasStableProcessEscapeRate`; its normal
attraction, tightness, spectral comparison, Rademacher calculations, and
normal-constant bridge are ordinary imports. The Rademacher distribution
module, the normal-constant lemma module, and the Gaussian escape-constant
entry build successfully together (3,985 Lake jobs).

## Abstraction review: stable balanced endpoint blocks (2026-10-19)

The balanced-partition limit used by stable endpoint cells had been exposed
from `StableLower/PathLimit.lean`, even though it depends only on deterministic
integer partitions and the stable specialization was used only by the cell
bridge proof. The general statement now lives in
`Analysis/Asymptotics/Scale/BlockScale.lean`:
if $H_n/n\to d>0$, $r_n\to\infty$, $r_n/n\to0$, $c_n>0$ eventually, and
$r_n/c_n\to a$, then the balanced block count tends to infinity, both
possible block lengths diverge, and each possible length divided by $c_n$
tends to $a$. This is independent of random walks, stable laws, and
Mogulskii scales, so it is the reusable public abstraction.

The stable specialization is now the single proof-chain lemma
`balancedStableCellBlock_asymptotics` in
`Stable/RandomWalkBounds/EndpointBandTransfer/StableLower/Lemmas/BalancedBlocks.lean`.
It derives the hypotheses for the generic partition result from the stable
Mogulskii scale. Its clients are the two cell constructions in `CellBridge.lean`,
so the specialization stays under `Lemmas/`. The five path-limit estimates
remain in `StableLower/PathLimit.lean`: source search confirms they are used
both by `CellBridge.lean` and by `Gaussian/Blocks/FixedDiffusiveBlock.lean`.
The module header lists those five probability interfaces and their
quantitative meanings. The `Rate` imports used only in proof terms are now
ordinary imports; the public signatures continue to name the stable scale
objects from their owning module.

The targeted Lake build of `BlockScale`, the new `BalancedBlocks` lemma,
`PathLimit`, `CellBridge`, and the dependent Gaussian path/block and stable
normal-domain modules completed successfully. The import-boundary audit also
passed with 10 public entries and 818 graph visits. The dependent Gaussian
modules now import `Gaussian.Interval` directly wherever they use the
Gaussian CDF positivity theorem, rather than relying on it being reexported
from the escape-constant development.

## Abstraction review: Mogul'skii equation (34) terminal-left chain (2026-10-19)

The equation-(34) proof now has a small set of reader-facing modules under
`Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/RandomWalkBounds/Bridge/`:
`Events.lean` defines the base and endpoint corridor events, `CdfEntrance.lean`
proves the finite-bridge comparison from the source CDF hypothesis,
`TerminalLeftAsymptotics.lean` gives the logarithmic ratio under a finite
positive limit of the stable factor, and `TerminalLeftDecay.lean` gives the
slow-variation version used by the theorem chain. Their module headers state
the corresponding probability estimates.

The auxiliary estimates specific to this chain are grouped under
`Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/RandomWalkBounds/Bridge/Lemmas/`.
The stable-domain base-corridor positivity estimate and the finite-bridge
logarithmic-ratio deduction live in `TerminalLeftAsymptotics.lean`; its
endpoint-corridor decay step lives in `EndpointCorridorDecay.lean`. The latter
uses the general stable scale and strict-stability interfaces, while its
endpoint event remains specific to Mogul'skii equation (34), so it stays in
this proof family. The endpoint positivity intermediate is private within
the helper module.

The old root asymptotics module had four proof-chain declarations beside its
single theorem entry. Those helpers have moved under `Bridge/Lemmas/`, leaving
the root module with the equation-(34) theorem. The targeted build of both
helper modules and the asymptotics and decay entries completed successfully
(3,908 Lake jobs).

## Abstraction review: spectral endpoint-window lower bound (2026-10-19)

`RandomWalkBounds/SpectralEndpointBands.lean` mixed a spectral endpoint-band
argument into the general random-walk bound directory. Its four intermediate
estimates had only in-file callers, and the final centered-unit-variance
transfer had one production caller in `Rate/Endpoint/Windows.lean`. The proof
chain now lives in
`RandomWalkBounds/EndpointBands/Lemmas/SpectralLowerBound.lean`: the four
single-file steps are private, and the final finite-variance endpoint-window
estimate is the only helper imported by the rate entry. The generic endpoint
window events and return-kernel iteration remain in
`RandomWalkBounds/EndpointWindows.lean`, where they serve the Donsker and
rate interfaces.

The axiom audit now prints the final transfer lemma; this covers its private
proof chain. The stale proof-route path was updated. The helper module, its
rate client, and the `Alpha2EndpointBands` axiom-audit module build with the
pinned toolchain.

## Mogul'skii subtree inventory (2026-10-19)

The current Mogul'skii tree has 162 Lean modules. `Theorems.lean` is its only
module at the subject root and records the source formulas and Lean entry
points for Mogul'skii's four main theorems; it marks Theorem 4 as an open
formalization. The ten first-level directories each group a mathematical
subject or regime, with theorem-specific derivations under nested `Lemmas/`.
The former empty `Stable/RandomWalkBounds/PartitionLower/` directory was
removed after its modules moved into `Partition/Lower/`.

A production-tree scan of 1,467 Lean modules found no directory with more than
eight direct modules and no same-stem `Foo.lean`/`Foo/` collisions. A separate
heuristic scan flagged 58 Mogul'skii module docstrings for manual review of
their public API inventories; this count is only a review queue, not a
determination that every flagged header is incomplete. Four empty source
directories found in the broader scan were removed. Header-by-header review
remains open.

## Mogul'skii API-header follow-up (2026-10-20)

The endpoint and terminal-left review added formula-bearing declaration lists
to 21 modules:

- `Bridge/Lemmas/{Comparison,EntrancePositivity,TerminalLeftGeometry}.lean`
  and `Bridge/TerminalLeftAsymptotics.lean`;
- `Endpoint/{BandTransfer,Return,StrictStable,Upper}.lean`;
- `EndpointBandTransfer/StableRate.lean`,
  `EndpointBandTransfer/StableLower/EndpointMass.lean`, and
  `EndpointBandTransfer/StableLower/Lemmas/BalancedBlocks.lean`;
- `FromIncrementLaw/Path/{Law,Realization,RealizationContinuousBoundary}.lean`;
- `TerminalLeft/Inputs.lean`,
  `TerminalLeft/Partition/{EnergyUpper,Lower/{EnergyLower,WidthRate}}.lean`,
  `TerminalLeft/PathClass/{InnerOuter,Relative}.lean`, and
  `TerminalLeft/Realization.lean`.
The headers now identify the event measures, rate denominators, finite bridge
comparisons, endpoint-band bounds, and inner/outer rate limits. A refreshed
name-only scan of the 162-module Mogul'skii tree reports four apparent name
omissions; manual inspection confirms that all four declarations are already
listed under their fully qualified namespace names. This scan checks names,
not whether every formula and hypothesis is described adequately, so the
statement-by-statement semantic review remains open.

All 21 affected Lean modules built together with the pinned toolchain (4,042
Lake jobs). The output contains existing linter suggestions in imported
modules; the build completed successfully.

## Branching-walk foundational API headers (2026-10-20)

The foundational branching-walk modules now state their public declarations
and the mathematical data they expose. This batch covers the step encoding,
mark maps and measurable slot events, set-valued populations and their
genealogy, and the conversion between sibling-closed branching walks and
trees. In particular, the population headers describe the generation-depth
and successor conditions and the prefix-membership conclusion; the step
headers describe presence, support, and the mark-threshold events.

All seven affected modules, including `Basic/Definitions.lean`, compiled
with the pinned Lean toolchain (1,792 Lake jobs). A name scan found additional
foundational genealogy and position modules without an explicit API list;
those remain in the manual review queue.

The follow-up added formula-level API descriptions to descendant and ancestor
relations, realized-particle slices, path displacement, and accumulated
positions. These headers make explicit that the genealogy relations are
defined by surviving address extensions, and that generation slices partition
their corresponding particle sets. The five affected modules built with the
pinned toolchain (1,791 Lake jobs).

The cloud and trajectory review then added API descriptions for the particle
cloud, geometric support, slice measures, measurable trajectory interface,
frontiers, lower-tail domination, and injective particle matchings. The
frontier header also now agrees with its nonempty example: a slice may be
nonempty while its least frontier is empty because its infimum is not
attained. The nine affected modules built with the pinned toolchain (1,916
Lake jobs).

A production-tree layout scan covered 1,467 Lean modules, excluding vendored
Mathlib and test-only sources. It found no directory with more than eight
direct Lean modules, no `Foo.lean`/`Foo/` name collision, no directory with
both `Lemmas.lean` and `Lemmas/`, and no empty source directories. The former
parameter-named directory is absent from the production tree; its modules now
live under `EndpointDeviation/FirstStage/`, and no production import refers to
the old path. This structural scan does not replace the open
statement-by-statement public API review recorded above.

The 2026-10-20 endpoint-deviation cleanup is committed as two focused changes:
the first-stage estimate modules are grouped under `EndpointDeviation/FirstStage/`,
and the former parameter-named directory is removed. Their theorem
identifiers still name the positive-`a` parameter regime; the directory now
names the first-stage role. The generic extended-real power-ratio inequality
used by the PZ estimate is exposed from `Analysis/Asymptotics/Power/`, while
the non-reusable cutoff and PZ assembly steps remain under `FirstStage/Lemmas/`.
The affected first-stage dependency chain built successfully with 4,710 Lake
jobs. These commits are on the GitHub `preflight` subtree branch; its remote
build is recorded separately in the active branch checks.

The 2026-10-20 spine-capacity review removed the old overloaded module layout
from `EndpointDeviation/Drawdown/Spine/Capacity.lean`. That entry now exposes
the affine-corridor first-stage low-count estimate used by
`Population/LowCount.lean` and `SecondStage/PZ.lean`. Its positive-parameter
window schedule remains in `Spine/Window.lean`, where it is a mathematical
object with its own measurable-window and upper-envelope statements. The
second-stage tube, parameter and endpoint bounds, random-walk estimates,
scale limits, and capacity-probability compositions form one theorem-specific
proof chain under `Spine/Lemmas/`: `Tube.lean`, `ParameterBounds.lean`,
`CapacityMarkov.lean`, `RandomWalkBounds.lean`, `Asymptotics.lean`,
`CapacityProbability.lean`, `FailureProbability.lean`, and `TwoPhase.lean`. A
source-use scan found no external clients of those intermediate declarations.
The generic monotone-corridor-to-drawdown inclusion stays in
`RandomWalk/SmallDeviation/Drawdown/Event.lean`; it is shared by the linear
drifted-tube estimate and this nonlinear spine corridor. The actual directory
name is `FirstStage/`; the positive-parameter condition remains encoded in the
mathematical declaration names.

A fresh production-tree scan counted 1,478 Lean modules, excluding `.lake`,
vendored dependencies, and test-only sources. It found no same-stem file and
directory pairs, no directory with more than eight direct Lean files, no
`Lemmas.lean`/`Lemmas/` collisions, and no empty source directories. The
`Spine/` directory has four direct modules, and its proof-only `Lemmas/`
folder has eight direct modules. All eight proof-chain modules and the
`Capacity.lean` public entry compiled with the pinned toolchain (4,678 jobs
for the proof-chain build; 4,658 jobs for the entry-module build).

The four cloud rank and leftmost-selection modules now list their public
interfaces using their mathematical statements. `Cloud/Rank/Slice.lean`
contains the general slice-rank definition and finite-order consequences;
`Cloud/Rank/Descendant.lean` gives the predicate-restricted rank and its
sibling-rank comparison; `Cloud/Order/DynamicSelection.lean` gives threshold
count domination and injective matching into dynamic leftmost selection; and
`Cloud/Order/Selection.lean` lifts those estimates to rankwise and
measure-level cloud domination. These modules are kept under their semantic
owners because they expose reusable rank and selection interfaces. All four
built together with the pinned toolchain (2,042 Lake jobs).

The Mogul'skii theorem entry is now a Lean module,
`Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Theorems.lean`.
It reexports the formalized statements corresponding to Theorems 1–3 and
records the source formula and formalization status for Theorem 4. Theorem 4
still has no Lean proof, so the entry marks its proof route as pending instead
of introducing an axiom or an unproved declaration. The supporting folders
remain grouped by reusable mathematical subjects such as `Path/`, `Scale/`,
`Stable/`, `Gaussian/`, and `Spectral/`; collecting these public interfaces
under one generic `Definitions/` or `Lemmas/` folder would obscure their
semantics and conflict with the rule that reusable APIs stay outside
`Lemmas/`. The entry module and its imports built with the pinned toolchain
(4,029 Lake jobs).

## Mogul'skii terminal-left partition hierarchy (2026-10-20)

The terminal-left partition modules were grouped under the compound directory
`RandomWalkBounds/TerminalLeftPartition/`, while the corresponding stable
modules already used `Stable/RandomWalkBounds/TerminalLeft/Partition/`.
The generic modules now follow the same semantic hierarchy at
`RandomWalkBounds/TerminalLeft/Partition/`: `Basic.lean`, `Events.lean`, and
`LowerProbability.lean` expose the terminal-left partition construction and
its probability bounds, while the deterministic endpoint-core gluing step
remains in `Lemmas/LowerGeometry.lean`. Imports changed to the new module
paths; the declarations still belong to the `Discrete` namespace. This
removes the opaque compound directory name without moving reusable event or
probability interfaces into `Lemmas/`.

## Gaussian product-parameter helper abstraction review (2026-10-20)

`Gaussian/Blocks/Lemmas/ProductParameters.lean` has two clients:
`Mogulskii/Blocks/Uniform.lean` and `Mogulskii/Rate/Partition/Finite.lean`.
Write $\gamma(I)=\mathbb P(Z\in I)$ for a standard normal random variable
$Z$. The first selects $0<c\leq1$, $\delta>0$, and $b>0$ so that
\[
 b+\operatorname{ENNReal.ofReal}\!\left(k\left(\frac{c}{m^2}+\delta\right)\right)
 < \prod_{j<k}\gamma\!\left(\left(-\frac{R}{\sqrt c},\frac{R}{\sqrt c}\right)\right),
\]
where $m$ is the endpoint margin, $R$ is the block radius, and $k>0$ is the
number of blocks. For a nonempty finite target family $F$, the second assumes
\[
 \operatorname{ENNReal.ofReal}\!\left(\frac{kc}{m^2}\right)
 < \prod_{j<k}\gamma\!\left(\left(
   \frac{x_{y,j}-R}{\sqrt c},\frac{x_{y,j}+R}{\sqrt c}
 \right)\right)
 \qquad (y\in F),
\]
where $x_{y,j}$ is the target center. It chooses common $\delta>0$ and
$0<b\leq1$ so that the strict inequality remains true after replacing the
principal cost by $k(c/m^2+\delta)$ and adding $b$, for every $y\in F$.
Both statements are parameter selections in the finite
partition lower-bound proof of Mogul'skii (1974), Theorem 3, Section 4,
p. 764; the source citation is in the Lean module header.

The abstraction candidates were checked against the pinned Mathlib revision
`380f2aafb622cb2c1c93dac545b6389083c68c51`. Its
[`Finset.exists_min_image`](https://github.com/maix00/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/Data/Finset/Max.lean)
chooses $x\in s$ with $f(x)\leq f(y)$ for every $y\in s$ when $s$ is a
nonempty finite set in a linear order. The corresponding
[official Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Max.html)
records this interface. The same pinned revision provides
[`Finset.prod_le_prod`](https://github.com/maix00/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean)
and `Finset.prod_le_one`, which handle factorwise product comparison. The
repository's `Probability.Distributions.Gaussian.FiniteProduct` separately
provides Gaussian interval-product positivity and symmetric-interval
monotonicity. These APIs supply the minimum, positivity, and product
comparison steps; the remaining strict-slack allocation is a short numerical
consequence of the finite minimum.

The same use scan found `prod_gaussian_Ioo_halfRadius_le_linearReturn` only
at its declaration. Its `y / blocks` shift is application-specific, and the
proof is just interval containment followed by `measure_mono` and
`Finset.prod_le_prod`; the pinned Mathlib product API already exposes the
general factorwise comparison. A generalized center-shift wrapper would still
be a thin composition of those APIs, so this unused declaration was removed
from the distribution module. `FiniteProduct.lean` now lists its two retained
public Gaussian-product theorems and exposes no linear-return-specific name.

The finite-target statement could be generalized to arbitrary finite families
of ordered values, but that would package `Finset.exists_min_image` with a
basic real-number slack argument rather than provide a distinct mathematical
operation. The first statement's cost $k(c/m^2+\delta)$ and both conclusions'
Gaussian interval products are specific to this proof family. Therefore the
two declarations remain together under `Gaussian/Blocks/Lemmas/` instead of
adding a public generic wrapper or moving a reusable Gaussian-product result
into the proof folder. They are ordinary `lemma` declarations because two
modules use them; `Lemmas/` describes their proof-chain role and does not make
them Lean-private.

The import boundary now matches this classification: `ProductParameters.lean`
publicly imports the Gaussian interval interface used in its statements and
imports the finite-product results and pinned Mathlib order/product modules
ordinarily for its proofs. `Blocks/Uniform.lean` directly imports the
finite-product theorem it uses in its own proof. The helper and both clients
compiled together with the pinned toolchain (3,431 Lake jobs).

## Stable Mogul'skii path-class rate header sign (2026-10-20)

The public theorem in
`Stable/RandomWalkBounds/PathClass/Rate.lean` concludes that the logarithm of
the path probability divided by `probabilityRateDenominator` tends to
`rateCoefficient α C * H`. The pinned definition in
`Probability/Process/Path/PathClass/StepCorridor/Probability/Normalization.lean`
is `rateCoefficient α C = -(C * 2 ^ α)`, and
`HasStableProcessEscapeRate.negative` gives $C<0$. The module header now
states the corresponding limit $-C2^\alpha H$ for its negative denominator.
The stable-domain interfaces that divide by the positive normalization retain
the limit $C2^\alpha H$; the two signs differ because their denominators have
opposite signs.

## Root-indexed field position API review (2026-10-20)

The module docstrings of
`Genealogy/RootIndexed/Field/{Positions,RelativePosition,Measurability}.lean`
now list all 35 public declarations with their mathematical meanings and the
relevant depth, measurability, and additive-structure assumptions.
`Positions.lean` owns the total and partial root-position constructions and
their reindexing and concatenation laws; `RelativePosition.lean` owns the
generation-relative process used by restart windows; `Measurability.lean`
owns the corresponding step-filtration and countable-selector results. These
statements remain outside `Lemmas/` because they expose the root-indexed
field's constructions and measurable interfaces, and remain in
`Genealogy/RootIndexed/Field/` because their types use that branching field
and its generation filtration.

The selector measurability proof uses the existing countable indexed-union
argument together with Mathlib's `MeasurableSet.iUnion` and coordinate
evaluation API; it does not introduce a generic measurable-selection
wrapper. The directly relevant Mathlib source was checked at the pinned
revision `380f2aafb622cb2c1c93dac545b6389083c68c51`. All three modules built
with the pinned project toolchain (3,133 Lake jobs). The broader
statement-by-statement module-header audit remains open.

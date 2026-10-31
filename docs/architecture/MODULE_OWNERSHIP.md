# Module ownership and abstraction boundaries

This document records where mathematical concepts belong and which Mathlib
objects the library builds on. It is intended to guide new definitions and
identify misplaced application-specific assumptions.

## Ownership map

| Concept | Owning layer | Existing interface or representative module |
| --- | --- | --- |
| Ulam--Harris addresses, generations, and deterministic trees | `Combinatorics/UlamHarris` | `Basic` owns address, root-indexed address, and mark-field types; `Generation` owns address lengths, generation differences, and equal-depth suffix-extension injectivity; `Order` owns the lexicographic order on root-indexed addresses; `Relation` owns the structural parent and direct-child relation; `Tree/` owns realized trees, their finite-depth and local-finiteness properties, topologies, and graph projections; `MarkedTree/` owns trees with marks restricted to realized vertices. Mathlib's [`RootedTree`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/SuccPred/Tree.html) and [`Quiver.Arborescence`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Quiver/Arborescence.html) use ancestor orders or directed unique paths; neither replaces the address-word representation with root-indexed labels. |
| Measurable structures and topologies on Ulam--Harris trees | `Combinatorics/UlamHarris/Tree/Topology` and `MarkedTree/Measurability` | `Tree/Topology/MeasurableSpace` owns the cylinder σ-algebra, `Borel.lean` compares it with the pointwise and truncation Borel structures, `FiniteLabels.lean` gives the finite-label equality, and `Metric.lean` owns the truncation metric. `MarkedTree/Measurability.lean` induces the marked-tree σ-algebra from its tree and mark coordinates. These are concrete tree-space interfaces built using Mathlib's generic coordinate-product measurable space and Borel-comap APIs; no tree-specific declaration belongs in a generic measure-theory layer. |
| Injective extension of equal-generation root addresses | `Combinatorics/UlamHarris/Generation` | `RootIndexed.appendAddresses_injective` states that appending arbitrary suffixes to distinct same-depth root-address pairs preserves injectivity; selected-subtree coordinates and rank-block coupling reuse it |
| Acyclicity from a graph height function | `Combinatorics/SimpleGraph/Acyclic/Height` | `SimpleGraph.isAcyclic_of_height` states that a height into any linear order makes a simple graph acyclic when each vertex has at most one adjacent vertex of height no greater than its own. Mathlib's acyclicity API contains path-uniqueness and bridge characterizations, while this height criterion is the general finite-cycle argument used by Ulam--Harris graph projections. |
| Positive compositions split at the first part | `Combinatorics/Enumerative/Composition/FirstPart` | Extends Mathlib's `Composition` object with the equivalence `Composition n ≃ Σ r : Fin n, Composition (n - (r.val + 1))` for `0 < n`, plus the induced finite-sum reindexing and first-block weight identities. Mathlib's `Composition.recOnSingleAppend` is an induction principle and does not provide this equivalence or sum formula. |
| Optional child configurations and deterministic branching walks | `Combinatorics/BranchingWalk` | `Step` defines optional child marks; `surviveAlong` and `BranchingWalk` give the realized-address and position model; `Genealogy/Survival` distinguishes descendants at every depth from one infinite lineage and applies Mathlib's inverse-system form of König's lemma under finite branching. `MarkedTree/Equivalence` converts sibling-closed step fields to and from marked realized trees; `SiblingOrderTransport` transports whole addresses when sibling slots are relabelled; `SiblingMonotonicity` relates step order to sibling-mark order; `OfBranchingWalk` constructs root-indexed marked trees from walks. Mathlib's [`RootedTree`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/SuccPred/Tree.html) uses the ancestor order, while [`Quiver.Arborescence`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Quiver/Arborescence.html) uses unique directed paths; neither models the optional slot labels and relative edge marks of these interfaces. `Walk/Basic` specializes the branching walk to a single lineage, `Walk/Equiv` identifies it with its initial position and optional increment sequence, and `Walk/Path/Position` connects its positions to `AdditivePath`. |
| Set-valued generations in a fixed branching field | `Combinatorics/BranchingWalk/Population` | `Offspring` owns the arbitrary parent-slot and child-address constructions; `Basic` defines generation-indexed populations and keeps layerwise finiteness as a separate property; `Genealogy` proves root, path, parent, and prefix consequences. These definitions have no probability-space or selection assumptions and form the deterministic population layer used by later measurable population processes. |
| Deterministic branching-walk data and path positions | `Combinatorics/BranchingWalk/Basic` | `FiniteSupport.lean` and `Ordering/Orderable.lean` lift step predicates to fields and root-indexed walks; `Sibling/` distinguishes sibling-closed fields from relabelable sibling-closable fields; `Position/` defines address-dependent additive displacement and positions from mapped edge marks; `Survival/Basic.lean` owns the time-free realized-particle set and its generation slices. These are complete branch-walk interfaces, not proof-only lemmas. The address-dependent displacement stays here: Mathlib's `Quiver.Path` represents composable arrows and their endpoints, while list folds and `mapAccumr` are generic traversals without this Ulam--Harris step-field semantics. |
| Optional-child steps and finite selections | `Combinatorics/BranchingWalk/Step` | `Basic`, `Count`, `Relation`, and `Measurability` define the optional-slot object and its coordinate interfaces; `Potential` projects marks to a measurable real value; `Measure/` owns the point-measure and exponential-weight observations. `Measure/ExponentialWeight` proves that finite negative (positive) total weight makes every lower (upper) real-potential level finite. `Selection/Finite`, `Selection/Slot`, `Selection/Potential`, and `Selection/ReserveSpine` define finite selections from an actual branching step, including the deterministic first/second reserve-slot rule and the potential-cutoff bound for the retained reserve slot; every selected slot lies in `support ξ`, and the specialized rules use slot order or real potential. `Selection/Potential` also owns the selected-first-slot positive-potential observable; its measurability theorem is in `MeasureTheory/BranchingWalk/Step/Selection/Potential`. The deterministic operations belong to `Combinatorics/BranchingWalk/Step/Selection`; measurable adapters belong to `MeasureTheory/BranchingWalk/Step/Selection`; random split events and cutoff laws belong to `Probability/BranchingRandomWalk`. The lower-finite order argument used to construct potential-first selections itself belongs to the generic `Combinatorics/Selection/NSelection/Mechanism/Infinite/Basic` layer. The coordinate product σ-algebra uses Mathlib’s generic `MeasurableSpace.pi` instance ([documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Constructions.html)); the duplicate step-specific instance was removed. |
| Order duality of real-marked branching steps | `Combinatorics/BranchingWalk/Step/Ordering` | `OrderDual.lean` maps every real mark through `OrderDual.toDual`, proves survival and support preservation, identifies the dual potential with the negative real mark, and transfers realized and total exponential weights without a probability law or countability assumption. The law-level tilted-spine identity stays under `Probability/BranchingRandomWalk/Spine/Tilted`. Mathlib provides the generic `OrderDual` type and `toDual`/`ofDual` maps, but not this optional-child-step and exponential-weight adapter ([Mathlib OrderDual documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/OrderDual.html); checked against pinned revision `380f2aafb622cb2c1c93dac545b6389083c68c51). |
| Ordered optional-child steps and slot normal forms | `Combinatorics/BranchingWalk/Step/Ordering` | `SiblingClosed` describes initial-segment support; `SiblingClosable` describes injective, support-covering relabeling into that form; `Monotone` and `ByPotential` own increasing/decreasing mark order and measurable ordered-step events; `Orderable` owns the increasing normal form and its finite-support existence theorem; `SiblingRank` counts surviving predecessors; `SlotOrder` gives finite prefixes of abstract slot orders; `MeasureInvariance` preserves point measures under reordering. The one-use mark-then-slot finite-rank construction is under `Lemmas/FiniteRank.lean` and is imported internally by `Orderable`, not exported as a public rank API. Mathlib's `Finset.sort` and `Finset.orderIsoOfFin` provide sorted finite lists and finite linear-order enumerations, while `orderIsoNatOfLinearSuccPredArch` supplies the generic ℕ slot representation; none directly states the support-covering self-relabeling of an optional child step. |
| Embedded space-time traces of deterministic branching walks | `Combinatorics/BranchingWalk/Trajectory` | `Basic` stores the vertex image as the existing `CloudSet Time X` and the edge image as a set in `Time × X`; `Step` constructs these from a marked step field; `Measurability` induces the coordinate σ-algebra and proves measurability of both coordinates and the vertex space-time set. Mathlib's `Quiver.Path` stores composable arrows and their endpoints, not the geometric space-time image, so it does not replace this trace object. |
| Generic capacity-$N$ candidate-set selection and its ordered and matching interfaces | `Combinatorics/Selection/NSelection` | `Basic` defines capacity-bounded subset selectors; `Mechanism/` owns ordered first-$N$ rules and order transport; `Matching/` gives generic Hall and equal-rank criteria. The inputs are candidate sets, finite sets, and order relations, giving this interface its candidate-set combinatorics semantics. Branching-walk generation semantics enter in `Combinatorics/BranchingWalk/Selection/NSelection/Walk/BranchingWalk.lean`, whose output is a walk with at most $N$ offspring per node. Mathlib places Hall matching in [`Combinatorics/Hall`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Hall/Basic.html) and low-level finite-set choice and ordering operations in [`Data/Finset`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html); this project supplies the capacity-$N$ selector interface connecting those generic candidate-set operations. |
| Measurability of generic ranked capacity-$N$ selection | `MeasureTheory/Selection/NSelection` | `Finite/ByValue`, `Finite/AtRank`, `Infinite/Basic`, `Admissible`, and `Infinite/Totalized` add measurable candidate maps and measurable value comparisons to the generic ranked selector. Their measurable-space assumptions place these adapters here; process and stopping-time evaluations have their own owners. |
| Branching-walk selection containment, coupling, and deterministic walks | `Combinatorics/BranchingWalk/Selection` | `Contain` and `WalkTransform` describe sub-walk selection; `Coupling/` carries cloud, offspring, one-step, and pathwise domination; `NSelection/Walk/` defines the deterministic selected walk from offspring sets and a capacity selector, with generation populations, clouds, frontiers, and speeds. `NSelection/Walk/BranchingWalk.lean` defines the branch-specific selection transform on entire branching walks. These are the points where the generic selector acquires BranchingWalk semantics. |
| Unmarked branching specializations and genealogy projections | `Combinatorics/Branching` | `Basic.lean` specializes branching walks to unit marks; `Map.lean` forgets spatial marks while preserving the genealogy; `Tree/Basic.lean` names the Ulam--Harris genealogy type in the branching namespace; `Tree/Genealogy.lean` identifies a tree with the genealogy of its unit-mark branching walk and constructs the converse genealogy from sibling-closed steps. These are complete model adapters, not proof-chain lemmas. The generic invariance `surviveAlong_map_iff` belongs beside the `surviveAlong` predicate in `BranchingWalk/Basic/Survival/SurviveAlong.lean`. Mathlib's [`Quiver.Arborescence`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Quiver/Arborescence.html) represents directed trees by unique paths in a quiver; it does not replace the project's ordered Ulam--Harris address-tree interface. |
| Genealogy relations and generation sizes of deterministic branching walks | `Combinatorics/BranchingWalk/Basic/Genealogy` | `Descendant.lean` defines reachability along surviving finite paths, `Ancestor.lean` gives the converse relation and its generation-distance slices, and `GenerationSize.lean` counts generation slices and proves pathwise recursion and extinction monotonicity. Fixed-length list finiteness uses Mathlib's [`List.finite_length_eq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Finite/List.html); the prior local proof was removed. |
| Structural parent of a root-indexed address | `Combinatorics/UlamHarris/Relation` | `RootIndexed.parent` removes the final label of an address and preserves its root. This operation has no branching-walk or survival assumptions. Mathlib's [`RootedTree`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/SuccPred/Tree.html) models one tree through an ancestor order, while [`Quiver.Arborescence`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Quiver/Arborescence.html) models unique paths from one root; neither directly owns the project's `Root × List α` address operation. |
| Random branching steps, fields, laws, and point-measure observations | `Probability/BranchingRandomWalk/Step` | `Presentation/` owns measurable coordinate sampling, its `P.map S` indexed law, and mark transport; `Law/MultiRoot` owns the BRW-specific root-indexed field law and finite- and arbitrary-root observations. The generic IID field law and coordinate-independence API for optional child-slot configurations is owned by `Probability/BranchingProcess/Offspring/FieldLaw`; BRW clients use that interface directly without a duplicate `stepFieldLaw` wrapper. `Assumptions/` owns raw-law boundary normalization, cross-child exponential weight, and ordered leftmost moment hypotheses; `Field/Basic` realizes random presentations as deterministic step fields; `Field/Update` proves measurability of generation-local replacement; `Field/FiniteWeight` states simultaneous all-coordinate finiteness under boundary normalization. `PointMeasure/` owns slot-multiplicity observations, their laws, and point-process adapters; `Position/Measurability` owns generation-filtration measurability. Mathlib's [`Measure.infinitePi` and `iIndepFun`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/InfinitePi.html) provide the generic product-law and coordinate-independence layer; these modules add the branching-step field and generation semantics. The deterministic step and point-measure objects remain in `Combinatorics/BranchingWalk/Step/`. |
| Split declarations along adapted branching lineages | `Probability/BranchingRandomWalk/Timing/Splits` | `Declared.lean` owns the event that a selected lineage reads a split mark at generation `n` and declares it at generation `n+1`, together with the first-declaration stopping-time theorem. The generic first-hit and one-generation event shift remain in `Probability/Process/HittingTime/Declarations`; the tree-specific event no longer sits in the deterministic Ulam--Harris layer. |
| Offspring configuration laws and Galton--Watson generations | `Probability/BranchingProcess` | `Offspring/` owns the law of complete optional child-slot configurations, mark maps, point-measure pushforwards, and the independently sampled address field; `GaltonWatson/` owns the presampled process law, descendant-field distribution and independence, and generation-size recursion and measurability. `GaltonWatson/Moments/Definitions.lean` defines the finite-slot moment quantities; `FirstMoment.lean`, `SecondMoment.lean`, and `PaleyZygmund.lean` expose their complete recurrences and probability bounds. The one-use finite-population and independent-field calculations are grouped under `Moments/Lemmas/`. `GaltonWatson/BoundedGrowth.lean` specializes the moment recurrences to finite-slot offspring. The fully abstract second-moment recurrence and probability bounds are owned by `Probability/MeasureTheory/Moments/SecondMomentGrowth.lean`. Mathlib’s [`Measure.infinitePi` and `iIndepFun` product-law interfaces](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/InfinitePi.html) supply the general product-measure and coordinate-independence layer; the offspring field modules specialize them to complete optional child-slot configurations. The generic address-field fresh-randomness interface in `BranchingRandomWalk/Genealogy/Exploration/Abstract/AddressFiltration` is shared by the unmarked `PUnit` Galton–Watson model, so the generation module reuses it rather than maintaining a duplicate. The Galton–Watson generation and moment results are the unmarked `PUnit` specialization; marked offspring fields, spatial displacement, and branching-random-walk selection remain under `Probability/BranchingRandomWalk/`. |
| Time-indexed deterministic particle clouds, geometry, and extrema | `Combinatorics/BranchingWalk/Cloud` | `Basic` defines the labelled particle cloud and its geometric `CloudSet` image; `SliceMeasure` records one Dirac atom per particle; `Measurability` gives the coordinate σ-algebra; `Frontier` defines attained slice extrema and potential extrema. `Rank/Slice` owns cardinal rank within a time slice. These are full deterministic interfaces; the particle labels preserve multiplicity when positions agree. |
| Branching-cloud slice order and particle domination | `Combinatorics/BranchingWalk/Cloud/Order` | `Slice` defines rankwise order on cloud slices and transfers it to `Measure.LowerTailDominates`; `Domination` lifts this relation across time; `SliceDominatingMap` records the pathwise matching invariant consumed by several coupling modules; `DynamicSelection` and `Selection` transfer it through first-`N` selection. The generic labelled-set map lives at `Order/DominatingMap`. |
| Additive paths, finite block sums, and their topology | `Algebra/BigOperators` and `Topology/Algebra/BigOperators` | `AdditivePath` owns finite displacements and block identities; `Topology/Algebra/BigOperators/PartialSum` proves continuity of the generic finite partial-sum map for topological additive commutative monoids with continuous addition. |
| Finite weighted-sum comparison bounds | `Algebra/Order/BigOperators/WeightedSum` | Bounds a weighted sum against the total mass when the masses are nonnegative and the weights lie in a fixed interval; the undivided bound assumes an ordered commutative ring, and the quotient bounds assume an ordered field |
| Natural exponents from real logarithmic ceilings | `Analysis/SpecialFunctions/LogarithmicCeiling` | Packages Mathlib's `Real.logb`, real-power monotonicity, and natural ceiling into $x\le b^{\lceil\log_b x\rceil_+}$ for $x>0$ and $b>1$; this is the reusable real-analysis estimate used to select integer exponential horizons. |
| Continuous additive maps from nonnegative reals | `Analysis/FunctionalEquation/NNReal` | `map_nnreal_smul` extends Mathlib's `map_real_smul` from a real-vector-space domain to $\mathbb R_{\ge0}$: a continuous additive homomorphism into a Hausdorff topological real vector space is determined by its value at $1$. Its `AddMonoidHomClass` interface is shared by stable characteristic-exponent and characteristic-function arguments. |
| Algebra of normalized finite weighted sums | `Algebra/BigOperators/WeightedSum/Cancellation` | Gives the normalization, weighted-average, and weight-cancellation identities for finite sums over an arbitrary field, without a probability-law assumption |
| Countable ENNReal sums over ordered pairs | `Topology/Algebra/InfiniteSum/ENNReal` | `PairPartition.lean` gives the diagonal/off-diagonal decomposition for any countable index type and arbitrary pair weight; model-specific uses remain with their probability or branching-process owners |
| Deterministic finite range, corridor, and feedback bounds | `Order/Bounds` | `Truncation` provides the reusable finite event-tail decomposition; `Feedback` gives endpoint, within-block, and real scaled-window bounds; `RangeCover` covers a unit-range tube by finitely many uniform corridors; `FiniteRangeTranslation` translates any nonempty finite family of pairwise diameter at most `w` into `[0,w]`; `Corridor` gives a generic one-jump path estimate. Each statement is an order/algebra interface used by path or probability owners, with the truncation formula retained as a reusable finite-family tool. |
| Set extrema transported through order duality | `Order/OrderDual/SetExtrema` | The image equivalences for `toDual` and `ofDual` require only `LE`; Mathlib's corresponding duality lemmas require `Preorder` |
| Finite affine grids and rational interval coordinates | `Order/Interval` | `UniformGrid` defines finite affine subdivisions in ordered fields; `DyadicGrid` specializes them to nested powers of two; `RationalGrid` represents finite rational families on such grids; `RationalCoordinate/UnitInterval` owns the rational subtype of $[0,1]$ |
| Lower-set restriction of set-valued families | `Order/SetDissipate` | `Set.dissipate_congr` extends Mathlib's `Set.dissipate`: if two families agree for every $y\leq x$, their dissipations at $x$ agree; the result requires only `[LE α]`, so it also applies beyond natural-indexed sequences |
| Dense rational and dyadic coordinates on the real unit interval | `Topology/Order` | `UnitInterval/Rational` embeds rational coordinates into the real unit interval and proves dense range; `DyadicUnitInterval` gives the countable dense union of finite dyadic grids |
| Càdlàg paths, oscillation, jumps, range constraints, and uniform limits | `Topology/Cadlag` | `Basic` owns the path structure; `Oscillation` gives local one-sided variation bounds; `Jump` proves finiteness of jumps above a threshold and countability of discontinuities; `Range` defines path-range constraints and `IsCadlag.range_subset_of_dense` extends closed range bounds from a dense time set containing $\top$; `UniformLimit` proves closure under uniform limits into complete pseudo-metric state spaces. These are path-space interfaces, not proof-chain lemmas. |
| Continuous-path compactness, closed range constraints, interval corridors, and last-zero/sign-change maps | `Topology/ContinuousMap` | `Compactness` gives Arzelà–Ascoli compact-closure criteria for common moduli and oscillation bounds; `Range` proves that pointwise constraints into any closed subset of a metric state space form a closed set of paths; `Corridor` owns open/closed interval range constraints; `Oscillation` gives the finite corridor cover for zero-starting bounded-oscillation paths; `LastZero` and `LastSignChange` own deterministic measurable path functionals and terminal-excursion transforms. Their Brownian laws and probability consequences remain in `Probability/Process/Brownian`; the generic metric oscillation predicate remains in `Topology/MetricSpace`. |
| Skorokhod topology, corridors, path maps, and deterministic small-deviation sets | `Topology/Cadlag/Skorokhod` | `Topology.lean` installs the J₁ metric/Borel instances; `Corridor/{Basic,Dense,Endpoint,Upper,Weight}` owns uniform-margin open and closed corridors, their countable rational-coordinate descriptions, terminal constraints, one-sided upper events, and continuous cutoff weights; `Maps/Continuous` embeds continuous paths and `Maps/Range` forgets a state subtype isometrically; `SmallDeviation/PathSets` owns law-independent range tubes, endpoint windows, and segment extensions; `RangeCover` specializes the generic finite range cover to path sets. These are full deterministic path-space interfaces; measure and probability consequences stay in their owning layers.
| Skorokhod compactness and separability | `Topology/Cadlag/Skorokhod/Compactness` and `Topology/Cadlag/Skorokhod/Path/Separable` | `Compactness/MovingPartition` owns the reusable compact finite-parameter family of step paths with moving knots and its approximation-membership interface; `Path/Separable` owns the public countable-dense-set theorem and separability instance. The explicit countable parameter-family construction remains in `Path/Lemmas/Separable`. The finite family supports multiple compactness and separability clients, so it is not proof-only. Mathlib supplies compactness and separability primitives, but not these J₁ path-space interfaces. |
| Skorokhod path evaluation and integral functionals | `Topology/Cadlag/Skorokhod/Evaluation` | `Basic` gives J₁ evaluation continuity at continuity times; `Measurable` gives fixed-time Borel evaluation; `Joint` gives Borel measurability of $(f,t)\mapsto f(t)$; `Integral` gives continuity of bounded continuous path-integral functionals. Fixed and joint evaluation are both full interfaces: fixed-time measurability is a common reusable corollary and joint evaluation is used for variable-time constructions. The inner scalar-probe, right-grid, and dominated-convergence details remain private. Mathlib has generic measurable-function and càdlàg primitives but no evaluation theorem for this project’s J₁ path space.
| Skorokhod oscillation tubes, finite oscillation partitions, and double-excursion criteria | `Topology/Cadlag/Skorokhod/Oscillation` | `Basic` specializes `Metric.OscillationBounded` to path oscillation and owns its open and closed tubes; `Dense` gives the countable rational-coordinate descriptions; `Partition` owns finite partitions, cellwise bounds, step approximations, time-change pullback, measurability, and existence for càdlàg paths. `DoubleExcursion/Basic` and `DoubleExcursion/Converse` give the partition-to-modulus and modulus-to-partition implications. The one-use jump-location, jump-separation, and oscillation estimates live as package-internal proof support under `DoubleExcursion/Lemmas/JumpControl`; converse-only construction details remain private to `DoubleExcursion/Converse`. The pathwise moduli correspond to Patrick Billingsley, *Convergence of Probability Measures*, 1st ed., Wiley, 1968, Chapter 3, §14, Theorem 14.4, p. 119; the formalized implications are stated for metric-valued paths. |
| Bounded metric cutoffs and pairwise range oscillation | `Topology/MetricSpace` | `Cutoff` defines $x\mapsto\min(1,\operatorname{dist}(x,s^c))$ and proves continuity, the $[0,1]$ bound, and positivity exactly on open $s$ when $s^c$ is nonempty. `Oscillation` defines the generic function-level bound `Metric.OscillationBounded` and identifies it with the extended diameter bound on `Set.range f` using Mathlib's `Metric.ediam`; path-space and random-walk modules reuse this predicate. |
| Deterministic Skorokhod path-space interfaces | `Topology/Cadlag/Skorokhod/Path` | `Endpoint` gives the nonexpansive and continuous endpoint evaluations; `Separation` gives separation of the J₁ distance and approximate time-change minimizers; `Range` transfers closed state-range constraints to closed/Borel path sets; `Scaling` gives spatial scaling continuity; `Linear` gives linear-path error bounds; `TerminalLeft` constructs the D₀ endpoint convention. These are complete interfaces with independent clients, so they stay beside the path-space topology; only the countable dense step-path construction is under `Lemmas/`. The pinned Mathlib tree (`Vendor/Mathlib`, commit `380f2aafb6`) has the general `IsCadlag` order API but no Skorokhod/J₁ path-space module, so these interfaces extend rather than duplicate Mathlib.
| Linear paths in Skorokhod space | `Topology/Cadlag/Skorokhod/Path/Linear` | Reuses the canonical continuous map $t\mapsto at$ and owns its $J_1$ distance and uniform-error estimates; Brownian support arguments consume this path-space interface. |
| Terminal-left endpoint convention for càdlàg path spaces | `Topology/Cadlag/Skorokhod/Path/TerminalLeft` | `terminalLeftPath` and `terminalLeftPathSpace` define the modification $f(1)=f(1-)$ for arbitrary topological state spaces; the construction maps paths into the endpoint subspace when the state space is T₂. Borel measurability of the real-valued specialization belongs to `MeasureTheory/MeasurableSpace/CadlagPath/TerminalLeft`. |
| Affine parametrizations, unit-block time coordinates, and the named identity clock | `Topology/Order/UnitInterval/Time` | Reuses Mathlib's `unitInterval.toNNReal`, `Set.projIcc`, and `AffineMap.lineMap`; `unitInterval.terminalSegmentParameter` reparameterizes any terminal unit interval `[start,1]`, with its real coordinate characterized by `AffineMap.lineMap`. `unitInterval.toNNReal_top` supplies the maximal endpoint value not separately named by Mathlib; `unitInterval.exists_mul_eq` and `exists_add_mul_eq` parametrize nonnegative and translated nonnegative intervals; `unitInterval.blockParameter` projects time into its unit block and sums to elapsed time; and `unitInterval.clock` names the identity coordinate used as a process clock |
| Càdlàg floor maps and limits from convergent order bounds | `Topology/Order` | `FloorCadlag` proves the integer- and natural-valued real floor maps are càdlàg; `Limit` gives the order-topological two-index squeeze result when every fixed approximant converges and the approximating limits converge to the same value |
| Extended-real limit rules for real-valued functions | `Order/EReal` | `LiminfLimsup` states arbitrary-filter translation and vanishing-perturbation formulas for `EReal` limsup and liminf; multiplicative scaling uses Mathlib's `EReal.limsup_const_mul_of_nonneg_of_ne_top` and `EReal.liminf_const_mul_of_nonneg_of_ne_top` directly |
| General filter limits and slow diagonal selection | `Order/Filter` | `LiminfLimsup` identifies bounded limsups and liminfs under a vanishing difference for densely ordered, conditionally complete topological additive groups with continuous addition and negation; `SlowDiagonal` selects monotone $d_n\to\infty$ with $P(d_n,n)$ eventually from eventual validity for each fixed parameter. Quantitative real-sequence error constraints belong to `Analysis/Asymptotics/Sequence/SlowDiagonal` |
| Finite ordered-family range translations | `Order/Bounds` | `FiniteRangeTranslation` places values of `x:ι→G` on any nonempty finite set `s⊆ι` inside `[0,w]` in a linearly ordered additive group, provided `|xᵢ−xⱼ|≤w` for all `i,j∈s` |
| Deterministic process-time grids and rounding time functionals up to grids | `Probability/Process/TimeGrid` | `UnitInterval`, `Expanding`, `Dense/NonnegativeRationals`, `Ceiling`; the ceiling selector specializes Mathlib's `MeasureTheory.hittingBtwn` and its convergence theorem is independent of paths and probability laws |
| Balanced finite block-length lists | `Combinatorics/Sequence/BalancedPartition` | Given a total horizon $N$ and reference length $r$, constructs $q=\lfloor N/r\rfloor$ near-equal natural-number block lengths whose sum is exactly $N$; each length is one of the two adjacent integers around $N/q$. Mathlib's `List.splitLengths` consumes an already supplied length list, while this constructor creates the balanced list from quotient and remainder data. |
| Finite sequence blocks and variable-length block starts | `Combinatorics/Sequence/Block` and `TailMergedBlock` | `Block` defines a length-`ℓ` window of any sequence, its default-padded form, and the prefix-sum start index for arbitrary natural block lengths. `TailMergedBlock` schedules quotient-length blocks on a finite interval and absorbs the remainder into the last block. These sequence-level constructions have no value-space or probability assumptions; additive displacement identities live beside `AdditivePath`. |
| Cyclic gaps and cyclic-subset/composition reindexing | `Combinatorics/Sequence/CyclicGap` | `Basic` represents the positive wrap-around gap lengths and rotated path segments of a nonempty subset of `Fin n`; `Reindex` gives the bijection with a positive composition of `n` marked by an offset in its final part and the corresponding weighted finite-sum identity. This extends Mathlib's linear `Composition` and boundary-set API to cyclic starts; only the inverse-construction proof is under `Lemmas/`. |
| Finite-sequence leaders and Riesz's combinatorial lemma | `Combinatorics/Sequence/Leader` | Defines the leader indices of partial sums and proves that the sum of their increments is nonpositive in a linearly ordered additive commutative group. The general combinatorial theorem is consumed by the Kingman subadditive-ergodic proof. |
| Asymptotic limits for balanced block lengths | `Analysis/Asymptotics/Scale/Block/Partition` | If the reference length and quotient block count diverge, the short and long block lengths preserve the reference scale; the complete partition theorem also transfers a positive-density horizon and a reference-to-clock limit. The finite combinatorial construction is imported from `Combinatorics/Sequence/BalancedPartition`. |
| Deterministic asymptotic scales and limits | `Analysis/Asymptotics` | `Scale/Basic` owns `IsSmallDeviationScale`; `Scale/Inverse`, `Scale/Block`, and `Scale/Power` own the discrete inverse, rounded block, and power-scale APIs. `Sequence/` owns general real-sequence limit tools, including `SqrtRatio` ($a_n^2/b_n\to0$ implies $a_n/\sqrt{b_n}\to0$ under its sign hypotheses) and the error-constrained slow diagonal; regular-variation results remain under `RegularVariation/`. |
| Finite exponential sums under a diverging scale | `Analysis/Asymptotics/Sequence/ExponentialSum` | For any finite $F$, $g\to+\infty$, and a common gap $\delta>0$, the bound $e_i/g<c-\delta$ eventually for every $i\in F$ implies $\sum_{i\in F}\exp(e_i)\leq\exp(cg)$ eventually, including $F=\varnothing$; the proof absorbs $|F|$ using $|F|\leq |F|+1$. This is related to, but has a different interface from, pinned Mathlib `ExpGrowth.expGrowthSup_sum`: Mathlib states a finite-sum identity for limsup exponential growth of natural-indexed `ℝ≥0∞` sequences, while this theorem handles arbitrary filters, real exponent families, and a separate diverging scale.
| Logarithms of power-bounded quantities | `Analysis/Asymptotics/Sequence/LogarithmicScale` | If $L\to+\infty$, $u\geq0$ eventually, $C\geq0$, $p>0$, and $u\leq C L^p$ eventually, then $\log(u+1)/L\to0$. This combines the pinned Mathlib logarithmic little-$o$ and power-limit interfaces into a reusable scale estimate.
| Finite logarithmic sums at a negative scale | `Analysis/Asymptotics/Sequence/LogSum` | Converts lower bounds on finitely many positive summands into a lower bound on the logarithmic rate of their sum; the asymptotic finite-sum limit also accepts one component attaining the minimal rate and a lower comparison for the target quantity. Empty-set and target-positivity assumptions are handled by the actual hypotheses rather than extra nonemptiness assumptions. |
| Comparisons of negative logarithmic ratios | `Analysis/Asymptotics/Sequence/NegativeRatio` | An additive error is negligible relative to a denominator tending to $-\infty$; a fixed multiplicative comparison of positive quantities gives the corresponding one-sided logarithmic-ratio bound as the smaller quantity tends to zero. |
| Uniform thresholds from sequential estimates | `Analysis/Asymptotics/Sequence/UniformThreshold` | For real widths and arbitrary admissible parameters, if every divergent width sequence and every sequence of admissible parameters eventually satisfy a predicate, one common real threshold works for all widths and parameters. This packages the contradiction selection used in WANG Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, proof of Lemma 3.5; the one-predicate sequential criterion is already covered by Mathlib's `Filter.eventually_iff_seq_eventually`. |
| First-order complex exponential asymptotics | `Analysis/SpecialFunctions/Complex/Exponential` | `Complex.tendsto_exp_mul_real_div` packages the real-parameter slope limit of `exp(tz)`; specialized Taylor bounds stay local to their proof when they only support one application |
| Real logarithmic cosine asymptotics | `Analysis/SpecialFunctions/Trigonometric` | `LogAsymptotics` owns the local logarithmic cosine limit, its $\pi/L$ specialization, and the resulting real-power limit under $L_n\to\infty$, $t_n>0$, and $L_n^2/t_n\to0$ |
| Cosine Tauberian kernel and its real Mellin estimates | `Analysis/Fourier/CosineTauberian` | The kernel, compact Fourier profile, power-weighted integrals, frequency-average coercivity, and regular-variation limit form a coherent analytic API; proof-only uses of Mathlib's complex Mellin transform stay ordinary imports |
| Positive-definite Fourier representation on `ℝ` | `Analysis/Fourier/Bochner` | `Theorem` states that continuous `φ : ℝ → ℂ` with `IsPositiveDefinite φ` and `φ 0 = 1` is the characteristic function of a probability measure; its one-use Fejér, inverse-density, and Gaussian-smoothing derivations are package-private under `Lemmas/` |
| Generic compact-system constructions | `Topology/Compactness/CompactSystem/Operations` | Extends Mathlib's `IsCompactSystem` with products, countable intersections, finite unions, finite intersections, sum and sigma systems, equivalence transport, finite-subset systems, and compact-interval systems; these results do not depend on analytic sets or capacities |
| Analytic sets, pavings, and capacities | Mathlib `MeasureTheory.Constructions.Polish.Basic`; project `MeasureTheory/Analytic/Paving` and `Capacity` | Mathlib owns the generic analytic-set predicate and continuous-image results. The project owns analytic sets relative to a paving and abstract capacity/Choquet results; a redundant local wrapper around Mathlib's continuous-image theorem was removed. |
| Measure operations, product estimates, and invariance under limits | `MeasureTheory/Measure`, `MeasureTheory/Integral`, and `MeasureTheory/OuterMeasure` | `Measure/Convolution/Power`, `Measure/Algebra/{DiracSum,IntegerValued}`, `Measure/InnerMeasure`, `Measure/EventLimits`, `Measure/Convergence/MapInvariance`, `Measure/Pi/FiniteReindexCover`, `Integral/MeasurePreserving`, `Integral/Lebesgue/RestrictLimit`, and `OuterMeasure/Finite/Cover`. Finite multiplicative recurrences are stated at the ordered-commutative-monoid level in `Algebra/Order/Monoid/Recurrence`; measure-process clients instantiate that generic result. |
| Finite-family and continuous-path tightness | `MeasureTheory/Measure/Tight` and `MeasureTheory/Measure/ContinuousMap/Tightness` | `Tight/FiniteFamily` states that the image of any finite index set under individually tight measures is tight; `Tight/Sequence` derives finite-prefix and eventual-uniform compact-mass criteria from it. `ContinuousMap/Tightness` gives Arzelà–Ascoli criteria from equicontinuity, moduli, and oscillation bounds. `ContinuousMap/RangeOscillation` bounds the measure of a continuous-path range event by its finite corridor cover. The path-specific finite-family proof now consumes the generic finite-image theorem. |
| Measurable finite partial sums | `MeasureTheory/Function` | `FinPartialSum` proves measurability of every finite partial-sum coordinate for a measurable additive monoid, without a topology assumption |
| Real Gaussian interval and sign facts | `Probability/Distributions/Gaussian` | `Interval` gives positivity of nonempty open intervals and strict centered CDF bounds; `Sign` gives half-line probabilities and their variance scaling. The one-client fourth-moment formulas are private under `Brownian/Construction/Lemmas/`, and the unused finite-product wrappers were removed in favor of Mathlib's `Finset` product APIs. |
| Rademacher and scalar-rescaled real distributions | `Probability/Distributions` | `Rademacher.lean` owns the two-point law, Boolean encoding, pushforward identity, and its integral and truncated-second-moment formulas; `Scaling.lean` owns the general positive-dilation identity $F_{rX}(x)=F_X(x/r)$ for every real threshold. Neither depends on a random-walk path model. |
| Characteristic-function defects, symmetrization, and tail Tauberian estimates | `Probability/Distributions/CharacteristicFunction` | `CosineDefect` owns the real integral defect and its characteristic-function identities; `Symmetrization/` gives the difference law, two-sided tail comparisons, and regular-variation transfer; `GaussianSmoothing` and `TruncatedMoment` connect defects to Laplace and truncated-moment quantities; `Tauberian/` transfers frequency-average and integrated-tail estimates to probability tails. Generic frequency kernels remain in `Analysis/Fourier/CosineTauberian`; `Zero` contains the independent midpoint estimate for a characteristic-function zero. |
| Logarithmic comparison for finite probability products | `Probability/MeasureTheory/FiniteProduct` | Converts a finite ENNReal product bound on measurable-event probabilities to the corresponding real logarithmic-sum inequality, in both inequality directions, under the precise positivity conditions needed by `toReal` and `log`. |
| Asymptotic probability rates and small-deviation scales | `Probability/MeasureTheory/Asymptotics` and `Probability/Process/Stable/SmallDeviation/EscapeRate` | `LogarithmicRate` gives generic transfers from finite products of exponential lower bounds and eventual power upper bounds to normalized logarithmic rates; `SmallDeviation` defines a scalar power-law small-deviation property, proves its radius-rescaling rule, and defines `smallDeviationEnergyCoefficient` for the full-width energy normalization. This scalar coefficient is independent of stable-process structure; the stable escape-rate layer owns the process escape rate itself. |
| Positive-probability sublevel events from first-moment bounds | `Probability/MeasureTheory/SmallValue` | `Basic.lean` proves that a measurable nonnegative ENNReal-valued random variable with expectation below $ρ$ is below $ρ$ with positive probability. The one-use Campbell adapter was removed; Poisson applications combine this result directly with the generic restricted-integral limit. |
| Logarithmic bounds for finite products of probabilities | `Probability/MeasureTheory/FiniteProduct.lean` | The two directions convert bounds on finite products of event probabilities into real logarithmic-sum inequalities, under positivity assumptions. Stable path-class rate clients use these generic probability interfaces. |
| Countable-selector evaluation and measurable finite-set filtering | `MeasureTheory/MeasurableSpace` | `CountableEvaluation` proves measurability of a countable-range selector and of evaluating a measurable field at that selector; `Finset/Filter` proves measurability of a Finset-valued map filtered by a sample-dependent predicate. Both are general operations over arbitrary measurable spaces and have clients in branching and path constructions. |
| Measurable continuous-path range constraints | `MeasureTheory/MeasurableSpace/ContinuousMap` | `Oscillation` makes the bounded range-diameter and zero-start subsets of continuous paths measurable |
| Lévy measures on the real line | `MeasureTheory/Measure/Levy` | `Basic` defines `IsLevyMeasure`; `Scaling` proves stability under nonzero dilation; `JumpRegions` owns the canonical unit small-jump set and arbitrary-radius large-jump sets; `Cutoff` owns the distinct reciprocal-band decomposition, cutoff selection, and finite intensity of every reciprocal large-jump band. The null-sphere selector used only in the Lévy–Khintchine representation is proof support under `Probability/Distributions/InfinitelyDivisible/LevyKhintchine/Lemmas/Representation/Lemmas`; its generic measurable-fiber ingredient is `MeasureTheory/Measure/LevelSet`. |
| One-sided tail thresholds and capped first moments | `MeasureTheory/Measure/Tails` | `Positive` turns positive mass on $(0,\infty)$ into a positive strict-tail threshold; `Power` integrates a two-sided tail bound $\nu(|x|>t)\le Ct^{-\alpha}$ with $\alpha<1$ to obtain $\int\min(R,|x|)\,d\nu<\infty$ |
| Measurable optional values | `MeasureTheory/MeasurableSpace/Option` | the disjoint-union measurable structure on `Option X`, measurability of `some`, `Option.map`, `getD`, and `elim`, and measurable presence events |
| Measurable filtering of finite-valued maps | `MeasureTheory/MeasurableSpace/Finset` | `Filter` proves that a measurable `Finset`-valued map stays measurable after a pointwise measurable, parameter-dependent filter; branching-step rules use this general result |
| Finite measure families and finite-partition bounds | `MeasureTheory/Measure/Finite` and `MeasureTheory/Measure/Partition` | `OnFamily` defines finiteness on an arbitrary family and its compact/one-sided ray instances; `Domination` derives a.e. family finiteness from an integrable dominating functional; `Partition` gives a finite disjoint-cell measure lower bound. Finite threshold sets from summable `ENNReal` weights use Mathlib’s `ENNReal.finite_const_le_of_tsum_ne_top` directly; the duplicate atom-finiteness wrapper module was removed. |
| Compact-range bounds and tightness for càdlàg path laws | `MeasureTheory/Measure/CadlagPath/Tightness` | `exists_eventually_compactRange_bound_of_real_error` converts compact-range probability estimates from real errors to arbitrary positive `ENNReal` errors for any filter of path laws; the tightness criteria combine common compact-range and oscillation-partition bounds, including eventual versions |
| Measure interfaces for càdlàg corridor path classes | `MeasureTheory/MeasurableSpace/CadlagPath` and `MeasureTheory/Measure/CadlagPath` | `MeasurableSpace/CadlagPath/Basic` defines the canonical dense-coordinate Borel embedding; `ContinuityTimes` identifies almost-everywhere continuity times; `Measure/CadlagPath/FiniteDimensional/Dense` gives finite-measure uniqueness from dense finite-dimensional evaluations; `PathClass/StepCorridor` owns corridor boundaries, event measurability, energies, and finite-partition approximations; `RangeCover` and `Support/Corridor` give measure and support criteria. The one-terminal-window corridor used only in the normal-domain endpoint proof is private under that proof's `Lemmas/` module.
| Pointwise and maximal ergodic theorems | `Probability/Ergodic` | `MaximalErgodic` proves the finite-measure Hopf/Garsia inequality; `Birkhoff` proves almost-everywhere convergence of averages to the conditional expectation on invariant sets and the ergodic integral corollary; `Invariant` gives the general monotonicity-implies-invariance criterion; `IIDShift` proves ergodicity of the one-sided shift on an i.i.d. product sequence by identifying invariant events with tail events and applying Kolmogorov's zero-one law. Mathlib supplies the Birkhoff-sum and mean-ergodic APIs, but no pointwise theorem for this finite-measure setting or packaged i.i.d.-shift ergodicity theorem. |
| Probability-law convergence and independence under weak limits | `Probability/ConvergenceInDistribution` | `Basic`, `Mapping`, and `Independence` cover convergence compatibility, continuous maps, and both directions of finite product/independence limits |
| Lower tails for finite iid event counts | `Probability/Independence/FiniteEventCount` | Gives the quarter-mean Chernoff bound for measurable event indicators of any finite independent, identically distributed family; Mathlib's `mgf_sum_of_identDistrib` and `measure_le_le_exp_mul_mgf` provide the general factorization and tail inequality, while this theorem records their Bernoulli specialization without branching assumptions. |
| Closed range constraints under weak convergence of càdlàg paths | `Probability/ConvergenceInDistribution/CadlagPath/RangeOscillation` | `limsup_measure_rangeOscillationLe_le_of_scalePath` combines closed-set Portmanteau with positive path scaling and the deterministic range-to-open-tube inclusion; it applies to arbitrary path-valued random variables and zero-start limiting laws, alongside the finite-dimensional càdlàg path limit interfaces |
| Second-moment convergence from probability-tail bounds | `Probability/MeasureTheory/Convergence/SecondMoment` | `FromTails`, `FromVaryingTails`, and `FromPolynomialTails` give second-moment convergence for fixed laws, varying laws, and polynomial tails; `Norm` transfers centered second-moment convergence to $L^2$, expectation, and variance. The one-sided first-moment endpoint estimate remains in `Probability/MeasureTheory/Convergence/TailExpectation`. |
| Moment inequalities and exponential-moment consequences | `Probability/MeasureTheory/Moments` | `PaleyZygmund.lean` gives the probability-space second-moment lower bound and its ENNReal support form; `ExponentialMoment.lean` gives an explicit logarithmic fourth-moment bound for the negative part under one finite exponential moment. Mathlib provides general moment integrability from an interior moment-generating-function condition, but not this quantitative bound. The geometric-recursion consequence remains in `SecondMomentGrowth.lean`. |
| Moving-level-set and second-moment tail integrals | `MeasureTheory/Integral/Convergence/IndicatorTail` and `MeasureTheory/Measure/Tails/SecondMoment` | The first gives the general dominated-convergence consequence $\int 1_{\{a_n\leq f\}}f\,d\mu\to0$ for integrable $f\geq0$ and $a_n\to\infty$; the second gives the real second-moment bound $a^2\mu(|x|\geq a)\leq\int 1_{\{a^2\leq x^2\}}x^2\,d\mu$. Both hold for arbitrary measures and serve multiple path-level applications, so their definitions and declarations belong in `MeasureTheory`. |
| Probability lower bounds from geometric second-moment recurrences | `Probability/MeasureTheory/Moments/SecondMomentGrowth` | Bounds $M_n/\rho^{2n}$ when $M_{n+1}=\rho^2M_n+v\rho^n$, then combines the bound with Paley--Zygmund for any nonnegative square-integrable random-variable sequence with mean $\rho^n$; branching-process-specific recurrences remain with their model. |
| Measurable counting-measure processes | `Probability/PointProcess` | `PointProcess` bundles a measurable map into Mathlib `Measure` with integer-valuedness and the chosen finite-on-family condition |
| Exponential tilts of random-measure laws | `Probability/RandomMeasure` | `ExponentialTilt` weights any measure by $e^{\theta F}$, maps the weighted measure through a measurable potential, and mixes the resulting laws; no counting-measure or point-process hypothesis is imposed |
| Poisson distribution moments and marked-event positivity | `Probability/Distributions/Poisson` | `Moments.lean` gives the first, second factorial, and ordinary second moments, variance, corresponding integrals, and the zero-rate law; `MarkedEvents.lean` combines a Poisson count or marked count with an independent, arbitrary nonnegative extended-real observable constrained below a threshold. Mathlib owns the Poisson law, its normalization, and the convolution theorem; these modules provide moment formulas and complete event estimates not present in that interface. |
| Poisson random measures and marked point-family laws | `Probability/RandomMeasure/Poisson` | `RandomMeasure/` owns finite random-measure observations and their laws, source-slot/count identities and single-atom restrictions in `SourceSlots.lean`, and finite-set count laws for sums of independent Poisson random measures in `Superposition.lean`; `PointFamily/Basic` owns finite atom families, their measurable realizations, and the coordinate-to-piece index; `PointFamily/Independence` derives independence of disjoint coordinate blocks; `Integration/` owns pathwise Poisson integral sums, Campbell intensity identities, the small-integral positive-probability cutoff, and the finite two-source window-vector interface; `Integrability/` owns finite-activity and first-moment transfers; `Intensity/TimeMark` owns unit-time product-intensity identities, `Intensity/Entrance` packages a finite-variation cutoff with a positive away-from-zero mark window, `Intensity/LevyCutoff` gives a reusable small-jump integrability consequence, and `Intensity/Support` transfers intensity-null sets and support signs to almost-sure facts about the realized measure; the one-use time-window product-integral step used only in characteristic-function proofs is module-private under `Intensity/Lemmas/` and imported with `import all`; `JumpPath/Basic` defines a cumulative marked-jump path and its one-point representation, while `JumpPath/Entrance/` gives the general two-source corridor-entrance model plus the supported endpoint and half-open increment identities; the one-use integral subtraction proof is private to `Entrance/Increment`, the path-specific absolute-integral estimate is private to `Entrance/Basic`, and the positive-probability cutoff for small Poisson integrals belongs to `Integration/SmallValue`; `Realization/` provides finite-jump event estimates and independent point-family constructions; `CharacteristicFunction/` owns the finite-piece, full-integral, independent-source, time-window, cutoff, and finite-dimensional characteristic-function APIs, while their one-use calculations remain in `Intensity/Lemmas/`. Mathlib's `poissonMeasure` is the Poisson distribution on $\mathbb N$ and its count-law API, rather than a marked random-measure construction, so this richer point-family interface stays in the project layer; see the [Mathlib Poisson API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Poisson/Basic.html). |
| Cutoff paths for Lévy Poisson configurations | `Probability/Process/Levy/Jump/PoissonConfiguration` | `Path.lean` identifies the canonical entrance path with its cutoff version and proves its almost-sure zero start; `Endpoint.lean` gives the cutoff-specific terminal identity; `Increment.lean` gives the cutoff-specific almost-sure half-open time-window formula. The general supported endpoint and increment identities are owned by `Probability/RandomMeasure/Poisson/JumpPath/Entrance`; `Intensity/Entrance/Canonical.lean` turns a finite-variation Lévy intensity and its cutoff bands into a positive-probability Poisson path-entrance model. The generic single-jump path and two-source construction are owned by `Probability/RandomMeasure/Poisson/JumpPath`, and the explicit one-jump corridor bound is in `Probability/Process/Corridor/PoissonEntrance`; this directory keeps the conclusions that depend on Lévy cutoff bands. |
| Lévy-process semantics and Brownian adapter | `Probability/Process/Levy` | `Basic.lean` defines the process interface through zero start, independent stationary increments, and almost-sure càdlàg paths; `PathContinuity.lean` proves $X_{t-}=X_t$ almost surely at every fixed $t>0$ from stationary increments and càdlàg paths; `Brownian.lean` proves Mathlib's real Brownian motion satisfies the interface without making the general definition depend on Brownian-specific assumptions. |
| Three-dimensional Bessel radial path law | `Probability/Process/Brownian/Bessel` | `ThreeDimensional.lean` constructs the triple product law, radial process, and path law; `Endpoint.lean` proves positivity of the time-one radius from the one-time Gaussian law and transfers it to the path law; `Support.lean` proves support for every nonnegative linear path. The path-law endpoint transfer needs continuity and measurability, while the underlying radius-positivity theorem does not. The coordinatewise radial-error estimate and its path-space transfer are single-client proof steps in `Bessel/Lemmas/Support.lean`. Mathlib's `abs_norm_sub_norm_le` is a generic norm reverse-triangle inequality, but it does not replace this coordinatewise estimate directly. Mathlib provides Brownian process laws and Bessel special functions, but no stochastic Bessel-process/path-law interface; the local radial construction therefore remains the model owner ([Brownian process API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/BrownianMotion/Basic.html), [Bessel special-functions API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Bessel.html)). The package cites J.-P. Imhof, “Density factorizations for Brownian motion, meander and the three-dimensional Bessel process, and applications,” *Journal of Applied Probability* 21(3) (1984), 500–510, Theorem 1, DOI 10.2307/3213612. |
| Brownian terminal-excursion (meander) law | `Probability/Process/Brownian/Meander` | `LastZero.lean` and `LastZeroLaw.lean` give the Brownian almost-sure facts and Iglehart path law; `LastSignChange.lean` identifies Bolthausen's transform with that law; `LastZeroSupport.lean` gives the support input used by conditioned-walk limits. The deterministic last-zero API is in `Topology/ContinuousMap/LastZero`, the sign-stable and endpoint-sign APIs are in `Topology/ContinuousMap/LastSignChange`, and their shared terminal affine clock is in `Topology/Order/UnitInterval/Time`; Brownian probability statements remain in the Brownian process layer. These four files state complete path-law, identification, and support results, rather than one-use proof stages. The headers cite Bolthausen (1976), Theorem 3.2, and Iglehart (1974), Section 3, Theorem (3.4). |
| Standard Gaussian Brownian witnesses and continuous modifications | `Probability/Process/Brownian/Construction` | `Existence.lean` obtains a pre-Brownian and continuous Brownian witness on the path-block space used by random-walk functional-limit results; `KolmogorovMoment.lean` gives the fourth-moment Kolmogorov bound for every `IsPreBrownianReal` process; `PreBrownianModification.lean` supplies its selected measurable, pathwise-continuous modification. Mathlib owns the Brownian process predicates, and the buildable BrownianMotion Kolmogorov–Chentsov theorem supplies the general modification result. The canonical BrownianMotion process construction is not currently importable with the pinned dependency because its transitive targets fail to build, so the repository's tight-source construction remains the local owner. |
| Markov processes and chains | `Probability/Process/Markov` | `Basic.lean` states the conditional-expectation Markov property using Mathlib kernels, separates transition-family composition from the process property, and derives the discrete-time kernel-power specialization; `Stopping/Basic.lean` defines the finite-stopping-time strong Markov property and proves that a discrete-time Markov chain satisfies it. |
| Ranked selection at a discrete stopping time | `Probability/Process/Stopping/Selection` | `Ranked.lean` applies the generic combinatorial rank selector to arbitrary time-indexed finite candidate sets and value maps at a `WithTop ℕ` stopping time, then proves measurability with respect to the stopping-time σ-algebra and the corresponding rank, membership, and injectivity laws. Its stopped-process and filtration semantics follow Mathlib's `Probability/Process/Stopping`; the underlying capacity selector remains in `Combinatorics/Selection`, and fixed-time selector measurability remains in `MeasureTheory/Selection`. |
| First-declaration and population-overflow stopping times | `Probability/Process/HittingTime` | `Declarations.lean` presents Mathlib's `hittingAfter` as an event-indexed first-success time, with finite-time, exact-time, one-generation-shift, and stopping-time laws; `PopulationOverflow.lean` defines the first time an arbitrary set-valued population exceeds capacity $N$, gives its cardinality characterizations and stopping-time criterion, and specializes to finite-set processes; `Geometric.lean` proves the measurable fibers and geometric mass formula $\mathbb P(\tau=k)=p(1-p)^k$ for independent events of common probability $p$; `ObservableCandidates.lean` gives a filtration-generic interface for candidate completion observability, countable candidate unions, and first successful completion times. `Examples/Lookahead.lean` contains finite-filtration counterexamples illustrating the adaptedness hypotheses. The official [Mathlib hitting-time API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/HittingTime.html) supplies the underlying process hitting time and adapted stopping-time theorem; its [independent-event API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html) supplies finite intersection products, while event-indexed success and population-overflow interfaces are reusable specializations. |
| Process corridor events, range, and one-jump entrance | `Probability/Process/Corridor` | `Segment.lean` owns the process segment increment, full-segment corridor and endpoint events, and their pathwise inclusion/monotonicity algebra; `Range.lean` relates rational-coordinate range events to complete-segment corridors and their finite cover, transfers rational range probabilities along an identical rational-coordinate process law, and extends rational interior oscillation bounds to the endpoint from a.s. càdlàg paths and fixed-time continuity; `ShortTime.lean` proves that a fixed centered rational-time corridor has probability tending to one as the time horizon tends to zero for an a.s. càdlàg process; the deterministic limit steps use Mathlib’s [`Function.leftLim`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Order/LeftRightLim.html) API; `PoissonEntrance.lean` proves corridor-entry probability from an explicit one-jump decomposition and does not assume a Lévy-process predicate. Càdlàg rational-coordinate characterizations and null-measurability stay in `Probability/Process/Path/Skorokhod/Corridor/Segment.lean`. |
| Brownian laws, modifications, reflection, and path-valued interfaces | `Probability/Process/Brownian` | `Construction/Existence` constructs the pre-Brownian process from the Gaussian random-walk path limit; `Construction/PreBrownianModification` provides the continuous modification used by the path-law and small-deviation clients; `PathLaw/` owns continuous and Skorokhod-valued representatives and their laws; `Reflection/Path`, `Reflection/FirstPassage`, and `Reflection/Descending` respectively own Brownian path consequences, reflection at first passages, and laws/increments of descending hitting times; `FiniteDimensional/UniformGrid`, `TimeReversal/`, and `Support/` provide the corresponding complete Brownian interfaces. The closedness of a pointwise path constraint is generic and belongs to `Topology/ContinuousMap/Range`, not to the Brownian probability module. The fourth-moment Kolmogorov input specific to this construction is internal under `Construction/Lemmas/`; generic path transformations and measure interfaces remain with `Probability/Process/Path` and `MeasureTheory/Measure`. |
| Path-space geometry, path-valued realizations, and generic tightness criteria | `Topology` and `Probability/Process/Path` | `Topology/Cadlag/Skorokhod` owns the path space, $J_1$ metric, time changes, and deterministic corridor and oscillation events. `Probability/Process/Path/Representation` turns coordinate processes into continuous or càdlàg path-valued maps and their image laws, with `Cadlag.lean` handling the almost-surely càdlàg realization; `Transform/Continuous` owns deterministic freeze, shift, and rebase maps on continuous path space; `FirstPassage`, `Extrema`, `Reflection`, and `TimeReversal` own the corresponding specialized path operations; `Skorokhod` and `PathClass/StepCorridor` connect those path objects to measurable tube events. `FirstPassage/Basic` specializes Mathlib's `MeasureTheory.hittingAfter` to evaluation of a continuous path and proves its infimum formula; `Prefix` gives path-locality, and `Measurability` proves closedness of hitting-by-$t$ sets and Borel measurability of the continuous-path passage time. `Restart`, `Reflection`, `Descending`, and `GridApproximation` state their full deterministic path interfaces. These build on Mathlib's `CadlagPath`, continuous-map Borel structure, and generic `hittingAfter`; Mathlib does not supply the path-specific continuity, restart, or path-space measurability results. See the [Mathlib càdlàg order API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Order/Cadlag.html) and [hitting-time API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/HittingTime.html). |
| First eligible unit-window times on continuous paths | `Probability/Process/Path/AboveStart/FirstWindow/Time` | `Core` defines window eligibility and the unrestricted and finite-horizon first times with their order characterizations; `Basic` gives the public measurability entry and countable-infimum relation; the rational-grid approximation proof used only for measurability is under `Lemmas/Approximation`; `Continuity`, `FiniteHorizon`, `RunningMinimum`, and `Tail` give reusable regularity, restriction, path-characterization, and probability-law interfaces. General positive-duration windows and their relation to monotonicity remain in `AboveStart/LocalMinimum`. The definitions are deterministic continuous-path objects; Brownian and random-walk hypotheses enter only in their application layers. |
| Skorokhod time changes and finite-partition clocks | `Topology/Cadlag/Skorokhod/TimeChange` | `Basic` owns the general time-change object as an `OrderIso` of `[0,1]` and derives its homeomorphism from the order topology; `LogDistortion` owns secant-slope and composition bounds; `FinitePartition` constructs the piecewise-affine knot-matching clock and its path/log-distortion consequences. `Limit/Convergence` gives the continuous-map uniform limit of cumulative clocks under a summable distortion budget; `Limit/Strict` upgrades it to a time change; `Limit/LogDistortion` proves stability of the distortion bound; `Limit/Tail` constructs tail limits and factors the global limit through each finite prefix. These are independently stated convergence interfaces, while the one-use estimates stay private in their proof modules. The single-use secant-slope estimate belongs in `FinitePartition/Lemmas/SecantSlope.lean`. |
| Strict Skorokhod corridors and their continuous weights | `Topology/Cadlag/Skorokhod/Corridor` | `Basic` owns open and closed path corridors and their $J_1$ topology; `Endpoint` adds terminal windows; `Dense` identifies rational-coordinate events with full-path corridors and proves their product-space measurability; `Upper` owns the one-sided open corridor; `Weight` specializes the generic metric cutoff to these path events. The unused prefix/remainder gluing interface was removed because it had no importers or named callers. |
| Skorokhod `J₁` and Billingsley logarithmic path metrics | `Topology/Cadlag/Skorokhod/EDistance` | `Basic` owns the pseudometric-level uniform and `J₁` extended-distance formulas; `Logarithmic/` defines Billingsley's cost, proves separation and topology equivalence, and records the quantitative conversion modulus. `Logarithmic/Completion/Completeness` is the public completeness entry point; generic summable path alignment remains in `AlignedCauchy`, while the Billingsley-specific subsequence extraction and aligned-limit assembly are grouped under the single `Completion/Lemmas/` subtree as package-private declarations. The unused tail-sum wrapper and one-use alignment steps are removed from the public API. Clock changes and their distortion remain in `TimeChange/`. |
| Finite step-corridor endpoint cores and inner-cell geometry | `Topology/Cadlag/Skorokhod/PathClass/StepCorridor/Partition` | `LowerCores` selects knot cores; `LowerGeometry` places finite real bounds in the common cells, without assumptions on a probability law |
| Finite step-corridor classes and continuous-boundary approximations | `Topology/Cadlag/Skorokhod/PathClass/StepCorridor` | `Boundary/Basic` defines finite right-continuous extended-real boundaries and their traces; `Boundary/Partition` owns the common finite knot partition and states that each boundary equals its right trace on the left-closed half-open cell; `Basic` defines the M₁/M₂ path classes and the continuous-admissibility criterion; `ContinuousBoundary` and `UniformGrid` give the continuous-boundary sandwich. The one-client terminal-window corridor constructor belongs in the Mogulskii endpoint proof's `Lemmas/` module. Mathlib supplies the general right-continuity interface in [`Topology.Order.Cadlag`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Order/Cadlag.html), while the common finite partition is specific to `StepBoundary`. |
| IID sequence laws, filtrations, independence, and block comparisons | `Probability/Sequence` | `Sequence/Block` owns finite-block coordinates and the measurable finite-block extension along `Fin.val` using Mathlib's `Function.extend`; `Sequence/IID/Basic` owns `iidSequenceLaw`, its finite-block product-law interface, and coordinate independence; `Sequence/IID/Blocks/` owns consecutive-block factorization, finite-cover and stopping-time interfaces, and `SpeedComparison.lean`, which compares an almost-sure normalized-position limit with the mean of IID block increments under pathwise bounds at block times |
| Geometric rewards along an IID trial sequence | `Probability/Sequence/IID/GeometricReward` | `Definitions.lean` owns the failed-prefix event and reward summand; `FirstMoment.lean` gives the exact IID first-moment identity and its failure-only and split-cycle consequences; `ExponentialTransform.lean` gives the ENNReal failure-cycle transform. The formulas apply to arbitrary measurable IID marks and rewards, and complement Mathlib's geometric waiting-time law. The one-use finite-prefix factorization steps are package-internal under `Lemmas/FailurePrefix.lean`. |
| Finite random-walk path events | `Probability/Process/RandomWalk/Path/Event` and `Path/Survival` | `Drawdown` owns finite-history drawdown and endpoint events with measurability; `Oscillation` owns the pairwise range-oscillation event, its measurability and increment-law probability, and horizon monotonicity; `LastSignChange` owns the terminal one-sign segment and its measurable start index. `Path/Survival/Basic` owns finite and infinite nonnegative-survival events, including the general measurable finite-partial-sum event for an additive monoid with a preorder. Short structural properties stay in their defining semantic modules rather than getting one-lemma files. |
| Random-walk information, martingales, and finite moments | `Probability/Process/RandomWalk/Path/Adapted` and `Path/Moment` | `Adapted/Filtration` specializes the sequence-prefix σ-algebra and consecutive-block independence to random-walk positions and increments; `Adapted/Martingale` gives the natural-filtration partial-sum martingale, square-submartingale, and maximal-inequality interfaces; `Moment/Fourth` specializes the generic independent-variable fourth-moment expansion in `Probability/Independence/Moment/Fourth` to IID random-walk sums and their maximal bound. The sequence filtration and independent-variable moment expansion remain at their generic owners. |
| Random-walk path corridors and horizontal-tube events | `Probability/Process/RandomWalk/Path/Corridor` | `Basic` owns open and closed corridor predicates on arbitrary time sets and their deterministic inclusions; `Affine` defines finite-history affine-corridor events, restart identities, measurability, and deterministic drawdown inclusions for generic real paths; `Horizontal/Basic` defines finite horizontal-tube events and their interval, reflection, rescaling, and width relations; `Horizontal/Core` adds measurability and IID probability interfaces; `Horizontal/StepPath` identifies those events with constant corridors for normalized step paths and transfers measurability; `Interpolation/Basic` proves the deterministic grid-vertex characterization of polygonal paths, and `Interpolation/Core` transfers it to the canonical IID path law. The continuous-path interval corridor itself is owned by `Topology/ContinuousMap/Corridor`. |
| Random-walk fluctuation and cyclic-survival estimates | `Probability/Process/RandomWalk/Fluctuation/SparreAndersen` | `Rotation/Cover` states the finite path cover; `Rotation/Basic` owns cyclic-survival events and their event identities and measurability; `Rotation/FiniteProduct` owns IID finite-product invariance and the endpoint-to-survival inequality; `Rotation/Probability` transfers that inequality to `iidSequenceLaw`; `Composition/InclusionExclusion` states the alternating-sum formula, with adjacent-block and gap-factorization proof steps under `Composition/Lemmas/BlockProbability/`. The generic product-measure reindexing uses Mathlib's `Measure.pi_map_piCongrLeft` API. |
| Drawdown events and small-deviation estimates | `Probability/Process/RandomWalk/SmallDeviation/Drawdown` | `Event.lean` owns $B_{L,\Delta,r}=\{S_i-S_j\leq\Delta\ (i\leq j\leq L),\ S_L\leq r\}$ and deterministic corridor consequences; `Scaling.lean` gives measurability and positive-rescaling identities. The finite-variance upper estimate is in `FiniteVarianceUpper/Theorems.lean`; the running maximum uses Mathlib’s `Mathlib.Order.PartialSups`; the floor-bin and jump-pattern decomposition is specific to this estimate. Its rounded-maximum, jump-pattern, conditional-block, and rate calculations, including the proof-specific block tube event, remain in `FiniteVarianceUpper/Lemmas/`. |
| Finite random-walk path windows | `Probability/Process/RandomWalk/Path/Window` | `Basic` owns deterministic finite-window and interval constraints with translation, block-coordinate, restart, and interval-shrinkage identities; `Core` owns measurability and the event indicator; `Endpoint` adds a terminal interval condition and its finite-block measurability interface. These related statements form module-level APIs, not separate files per lemma. |
| Random-walk polygonal paths and finite survival windows | `Probability/Process/RandomWalk/Path/Interpolation`, `Path/Representation`, and `Path/Survival` | `Interpolation/Basic` defines the normalized weighted-sum path and pathwise identities; `Core` owns its IID path laws; `Finite/Block` and `Finite/Grid` own finite-block laws and the complete uniform-grid endpoint estimate, with its arithmetic under `Finite/Lemmas/Grid`; `Scaling` and `Oscillation/` own path-level relations; `Path/Approximation` and `Path/Oscillation` own metric and probability approximations; `Limit/` owns the unbounded path, horizon restriction, and distributional transfers. `Representation/Scaling` defines the normalized step path from finite increments, and `Representation/Cadlag` gives its càdlàg unit-interval realization. `Survival/Interpolation` identifies eligible polygonal windows with discrete block survival; `Survival/Probability` gives positivity and horizon monotonicity for IID survival probabilities. |
| Hard-truncated random-walk increments and maximal path bounds | `Probability/Process/RandomWalk/Path/Truncation` | `Basic` defines the symmetric closed-cutoff increment $x\mathbf 1_{\{|x|\le r\}}$; `Moment` and `Asymptotic` give its moment, bias, and tail limits; `Maximal/` owns second- and fourth-moment block bounds; `Normalized` and `AdjacentBlocks` give complete prefix-event estimates; `Oscillation/Bound` gives the path oscillation probability bound, with one-use block-limit calculations under `Oscillation/Lemmas/`. The pinned Mathlib `ProbabilityTheory.truncation` is the generic half-open truncation $(-r,r]$, which differs at a possible atom $-r$; the symmetric convention is therefore kept explicit at this random-walk owner. Generic truncated-moment and measure-tail results stay in `Probability/Distributions/Moments/Truncated` and `Probability/MeasureTheory`. |
| Maximal increments and interpolation error | `Probability/Process/RandomWalk/Path/MaximalJump` and `Path/Interpolation/Path/Approximation` | `MaximalJump/Basic` owns the finite maximum of absolute increments, its pointwise bounds, and measurability; `FiniteVariance` gives the IID union bound and the finite-second-moment diffusive negligibility result. `Interpolation/Path/Approximation` uses that result to compare step and polygonal paths in the Skorokhod metric. The measure-generic tail estimates are owned by `Probability/MeasureTheory`, rather than nested under interpolation. |
| Couplings of probability measures and order comparison | `Probability/Coupling` | `Basic` defines a joint measure with prescribed marginals and its common-variable, product, swap, and map constructions; `Order` compares preimage probabilities for every measurable upper set under an almost-sure order; `Tail` specializes this to real upper tails |
| Adaptive event selection from independent variables | `Probability/Independence/AdaptiveChoice` | Finite disjoint past cells select measurable events of an independent future variable; binary choice and its finite-step iteration are derived from the finite-choice bound |
| General random-walk process laws and paths | `Probability/Process/RandomWalk` | path maps, kernels, Donsker and small-deviation interfaces |
| Normal random-walk limits and Donsker's theorem | `Probability/Process/RandomWalk/FunctionalLimit/Normal` and `.../Donsker` | `Normal/FiniteDimensional/CentralLimitTheorem` identifies the canonical IID walk with Mathlib's scalar CLT and gives its interval Portmanteau bounds; `Normal/BlockTail` provides the normal-domain local block estimates; `Normal/Tightness/Basic` proves the complete Gaussian-domain $J_1$ tightness theorem, with its compact-range, oscillation, and partition proof steps under `Normal/Tightness/Lemmas/`; `Normal/PathLimit/Basic` and `Brownian` state the Gaussian-domain path limits; `Normal/PathLimit/LinearTube` derives positive lower bounds for open $J_1$ balls around linear paths, including finite-variance and compact-slope forms; `Donsker/FiniteDimensional/Basic`, `Brownian`, `Grid`, and `Rational` progress from block-sum limits to Brownian endpoints, polygonal grid evaluations, and rational finite-dimensional limits; each stage publicly imports the objects in its theorem statements and ordinarily imports the preceding proof stage; `Donsker/Tightness/Path` exposes the oscillation estimate, explicit uniform path bound, and resulting tightness theorem, with its deterministic parameter choice under `Tightness/Lemmas/Parameters`; `Donsker/Path/Continuous` directly exposes its path, Brownian-process, IID-law, and convergence types, while importing rational finite-dimensional convergence and tightness as proof support; `Donsker/Path/` proves the continuous-path and Skorokhod invariance principles and groups the functional-limit corridor-to-tube adapters; `Donsker/Corridor/Brownian/Basic` gives open/closed Brownian corridor bounds, while `Endpoint` handles endpoint-constrained and scaled centered-tube consequences; entrance estimates remain under their semantic subdirectories |
| Survival-conditioned random-walk limits and transition estimates | `Probability/Process/RandomWalk/FunctionalLimit/Conditioned/{Survival,Meander,Transition}` | `Survival/` owns the finite-horizon conditioned increment law and scaling identities; `Meander/` identifies the centered first-window limit with Brownian meander and states the finite-variance conditioned path limit; `Transition/Event` defines the shared normalized corridor event and `Transition/DiffusiveLower` gives the complete diffusive lower bound. The one-use first-window factorization, finite-time limit, cyclic-rotation survival bound, and meander corridor transfers remain under the corresponding `FirstWindow/Lemmas/` and `Transition/Lemmas/` paths. Brownian meander path laws and support stay under `Probability/Process/Brownian/Meander`. |
| Brownian first-window times, shifts, and cutoff laws | `Probability/Process/Brownian/AboveStart/FirstWindow` | `Basic` gives almost-sure finiteness; `Continuity` and `EndpointHittingTime` give Brownian-law regularity and endpoint-return consequences; `Shift/` owns the uncentered and centered Brownian continuity, projected finite-horizon laws, and cutoff limit. The one-use Brownian positive-window, boundary non-atom, interior-return, and endpoint-return arguments stay in `Lemmas/`. The selector, time map, endpoint-return geometry, and centered/uncentered shift definitions are owned by `Probability/Process/Path/AboveStart/FirstWindow`. |
| Conditioned random-walk first-window limit | `Probability/Process/RandomWalk/FunctionalLimit/Conditioned/FirstWindow` | `Existence` proves almost-sure existence of a finite surviving window; `BlockLaw` proves the selected finite block has the survival-conditioned law; `Selection` identifies the selected index and rebased path law; `Limit` proves convergence to the centered Brownian first-window path. Bolthausen-specific prefix events, block factorization, and finite-horizon convergence steps are grouped under `FirstWindow/Lemmas/`. Brownian first-window path operations are owned by `Probability/Process/Path/AboveStart`, and the separate meander-law identification is owned by `Probability/Process/Brownian/Meander/`. |
| Finite paths relative to a restart schedule | `Probability/Process/Path/Restart` and `Probability/Process/RandomWalk/Path/Restart` | `Path/Restart/Basic.lean` defines the cutoff schedule and the generic finite-path relative-window predicate; `Measurability.lean` proves measurability under `MeasurableSub₂`; `Bounds.lean` gives the ordered additive endpoint estimate. In the random-walk specialization, `Windows.lean` connects the event to additive-increment histories; `Basic.lean` assigns its probability and proves initial-position invariance; `FirstMoment.lean` bounds the exponentially weighted restarted-window integral by an endpoint factor times the event probability and gives its horizontal-tube specialization; `Interval.lean` gives the IID closed-interval factorization; `Corridor.lean` specializes it to horizontal tubes. The interval-specific block-event calculation used only in that proof is under `Lemmas/IntervalFactorization.lean`, reusing the general variable-length IID block-event factorization. |
| Finite increment blocks, oscillations, and IID block laws | `Probability/Process/RandomWalk/Path/Block` | `Basic` owns block-sum measurability; `Measurable` owns the finite block-maximum event; `Oscillation` defines full and half-open partial-sum range events and their measurability. `Law/` identifies translated block-sum and oscillation laws, proves independence for consecutive variable-length blocks, and groups excursion, first-crossing, finite-interval, stopping-time, and two-excursion probability interfaces. It composes Mathlib's generic `iIndepFun` and product-measure APIs with the repository's block-coordinate maps. |
| IID random-walk block maximal estimates | `Probability/Process/RandomWalk/Path/Block/Maximal` | `Basic` specializes Mathlib’s Doob maximal inequality to deterministic IID increment blocks; `Fourth` gives the centered finite-fourth-moment form; `SecondMoment` states the centered unit-second-moment bound, its absolute-value event form, finite-scale ratio estimate, and diverging-scale consequence. These complete event bounds are reused in block partitions, Donsker tightness, and corridor comparisons. |
| Random-walk block corridors and second-moment comparisons | `Probability/Process/RandomWalk/Path/Block/Corridor` | `Basic` defines strict partial-sum corridor and endpoint events; `Measure` proves their measurability; `Geometry` gives the deterministic displacement and shrunken-corridor inclusions; `Core` turns the margin dichotomy into a distribution-free probability bound; `CoreReturn` defines the finite-block endpoint-core event and its pathwise consequences; `FiniteBridge` packages a finite prefix cover and IID bridge cells into a weak-limit comparison; and `SecondMoment` adds the centered finite-variance error and its uniform diffusive-block form. Mathlib’s [`MeasureTheory.maximal_ineq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/OptionalStopping.html) supplies the process-level Doob inequality; these modules provide the random-walk event interfaces and path-specific compositions. |
| Random-walk partitions of step corridors | `Probability/Process/RandomWalk/Path/Block/Partition` | `Basic` gives deterministic equal-block identities; `Normalized` transfers block-sum approximation to endpoint margins; `Core` gives measure comparisons with finite exceptional-block sums; `Maximal` specializes them to centered finite-variance increments. `CoreReturn/Endpoint` propagates knot-core bounds from consecutive local endpoint-core events; `CoreReturn/Geometry` transfers these cores and the cell constraints to a global strict corridor; `CoreReturn/Probability` combines that event inclusion with variable-length IID block factorization to obtain product lower bounds. `Range` gives variable-length partition-cell products and the finite-horizon IID inequality $\mathbb P(\operatorname{range}(S_0,\ldots,S_N)<w)\le\mathbb P(\operatorname{osc}(S_0,\ldots,S_m)<w)^q$ when $qm\le N$; `StepCorridor` gives arbitrary step-boundary floor-grid indices, global-to-cell constraints, and selected-cell range products. The modules impose no Mogul'skii scale or stable-law assumptions. |
| Terminal-left partitions for normalized random-walk paths | `Probability/Process/RandomWalk/Path/Skorokhod/TerminalLeft/Partition` | `Definitions.lean` defines the clipped terminal-left knot index and cell lengths; `Basic.lean` gives common-grid path evaluation and the normalized cell-length limit; `Lemmas/Index.lean` contains the internal index, endpoint, and last-cell calculations. `CellBounds.lean` transfers a terminal-left corridor constraint to selected half-open cells and bounds its IID probability by their range-probability product. The hypotheses are finite step boundaries and an IID real increment law, with no stable-law or asymptotic-scale assumptions. Mogulskii-specific lower geometry and product assembly remain under `SmallDeviation/Mogulskii/Lemmas/TerminalLeft/Partition/`. |
| Mogul'skii small-deviation theorem entry | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Theorems.lean` | The sole direct Lean file at the Mogul'skii root is the import entry for the four original article theorems; it identifies the formalized interfaces for Theorems 1–3 and records that Theorem 4 remains unformalized. The sibling `Gaussian/`, `Stable/`, `Rate/`, `Scale/`, and `Path/` directories own mathematical interfaces; theorem-specific derivations stay under `Lemmas/`. Generic terminal-left partition bounds live with their path owner, and Mogulskii-specific lower geometry and product assembly remain under `Mogulskii/Lemmas/TerminalLeft/Partition/`. Within `Stable/Discrete/`, `EscapeRateLowerBound.lean` exposes the complete discrete endpoint-return transfer estimate from a stable-process escape rate; its positivity and real-log helpers remain under `Stable/Discrete/Lemmas/`. `Stable/Discrete/Partition/{EnergyUpper,Upper,Limit}` contains the finite-partition upper and exact-rate interfaces; `Partition/Lower/{EnergyLower,WidthRate}` gives the lower-rate interfaces. The positivity and logarithmic-coboundedness step is proof support under `Stable/Discrete/Lemmas/Partition/Positivity.lean`; the balanced-core count is adjacent under `Lemmas/Partition/`. The endpoint-core block-product proof remains under `Partition/Lower/Lemmas/BridgeProduct.lean` and is shared by the positivity and width-rate steps. The one-cell range-rate estimate is in the `Stable.Discrete` namespace because both ordinary and terminal-left endpoint conventions use it. Under `TerminalLeft/Partition/`, the upper, lower, and exact energy-rate results remain complete rate interfaces; `TerminalLeft/PathClass/{Rate,InnerOuter,Relative,Regimes}` and `TerminalLeft/Realization` give the corresponding path-class, relative-approximation, regime, and arbitrary-IID-realization theorem forms. |
| Normal-domain discrete Mogul'skii rates | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Discrete/FromIncrementLaw/Normal` | `Normalization` constructs positive Gaussian norming inputs by changing a finite prefix while preserving eventual equality and the attraction limit; `Domain` packages the rate data from a normal-domain source; `FiniteVariance` specializes it to centered finite-variance increments; `ContinuousBoundary` exposes the continuous-boundary and finite-corridor rates; `HorizontalTube/{Basic,Scales,EndpointWindow}` gives the closed-tube core theorem and its scale and endpoint-window forms. The one-use terminal-left-to-horizontal-corridor conversion is under `HorizontalTube/Lemmas/EndpointWindowCorridor`. These modules are theorem interfaces at the normal-domain specialization layer, while comparison with the source proof remains partial for the rate derivation. |
| Mogul'skii diffusive scale specialization | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Scale` | `Basic.lean` defines $a_n\to\infty$ and $a_n/\sqrt n\to0$ as a specialization of `Asymptotics.IsSmallDeviationScale`. The standard $n^{1/4}$ witness is used only while proving the Gaussian escape coefficient and is derived there from the general power-scale theorem; no separate public witness module is retained. The floor-rounded block length $b_n=\lfloor c a_n^2\rfloor$ and its complete-block limits are owned by the scale-generic `Analysis/Asymptotics/Scale/Block/Diffusive.lean`. |
| Finite-boundary Mogul'skii rates | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Rate` | `Energy.lean` defines $H_\alpha(f,g)=\int_0^1(g(t)-f(t))^{-\alpha}\,dt$ and its algebraic identities. `Partition/Finite` gives the complete finite-Gaussian-reference lower-rate statements, while `Partition/Cover` gives a distinct interval-level sufficient-condition theorem; the one-use compact interval net is in `Partition/Lemmas/FiniteCover.lean` and reuses Mathlib’s totally bounded finite approximation. Step-corridor energies with extended-real boundaries remain in `MeasureTheory/Measure/CadlagPath/PathClass/StepCorridor/Energy.lean`. |
| Scalar domains of attraction for normalized i.i.d. sums | `Probability/Distributions/DomainOfAttraction` | `Basic` defines the centered normalized sum and fixed-normalization attraction predicate; `Normalization` transfers the limit under changing scales; `Block` handles varying block lengths; `Centering` derives zero mean from uncentered attraction; `CharacteristicFunction` gives the finite-sum transform and its limiting consequences |
| Variable-length random-walk block paths | `Probability/Process/RandomWalk/FunctionalLimit/NormalizedStep/Block` | `normalizedStepBlockCadlagPathIcc` and its law encode a block with independently varying time and space scales; weak-limit bounds for the resulting path events belong to `Probability/ConvergenceInDistribution` |
| Rademacher finite-interval paths, range events, and tube spectrum | `Probability/Process/RandomWalk/Rademacher/FiniteInterval` | `Path`, `KilledKernel`, and `Matrix` define the finite killed walk; `Range/` identifies lattice paths and gives range and corridor-survival bounds; `Spectral/` owns the explicit sine basis, survival estimates, and terminal-target analysis. The six modules in `Spectral/Target/` form the target-mass interface: coefficient, spectral expansion, extremal modes, lower bound, path interpretation, and diffusive limit. `Spectral/Survival/Asymptotics/CenteredTube` gives centered-tube limits for arbitrary radii and real spatial scales. Generic rounded centered-lattice radii and effective-width limits are owned by `Analysis/Asymptotics/Scale/CenteredInterval.lean`, which is shared with Brownian and stable-process estimates. The duplicate existential row-sum wrappers were removed in favor of the generic bounded-eigenfunction estimate in `LinearAlgebra/Matrix/FiniteKernel/Eigenfunction.lean`. |
| Finite-horizon kernel survival, returns, and bridges | `Probability/Kernel/Survival` | remaining mass, restriction to measurable cores, variable return-block sequences, final bridges, and sub-eigenfunction bounds |
| Killed increment kernels and return/entrance bounds for random walks | `Probability/Process/RandomWalk/Kernel/Killed` | `Basic`, `Comparison`, and `Partition` define and compare killed IID-increment kernels and identify their block events; `Return/` owns endpoint laws, bridge and entrance bounds, path-event comparisons, and uniform return iteration; `Survival/` transfers block bounds to horizontal-tube and uniform survival probabilities. Generic kernel iteration remains in `Probability/Kernel/Survival`; this layer supplies the additive random-walk adapter. |
| Markov-kernel powers | `Probability/Kernel/Markov.lean` | `IsMarkovKernel.pow` proves that every natural power of a Markov kernel remains a Markov kernel; it is the general kernel-level closure fact used by discrete Markov-chain transitions |
| Brownian corridor and range probabilities, and random-walk horizontal-tube estimates | `Probability/Process/Brownian/SmallDeviation` and `Probability/Process/RandomWalk/SmallDeviation/HorizontalTube` | `Corridor/{Bounds,Endpoint}` owns Brownian survival in centered intervals and the terminal-interval extension, with its finite-walk spectral and Donsker proof chain under `Corridor/Lemmas/`; `Range/` owns the standard escape constant, fixed finite spectral cover, and small-width logarithmic upper rate, with its Donsker transfer and spectral-limit proof stages under `Range/Lemmas/`; random-walk horizontal tubes own Donsker lower bounds and logarithmic-rate transfer under positive rescaling of increments |
| Random-walk range and block-oscillation small deviations | `Probability/Process/RandomWalk/SmallDeviation/Range` | `BlockDonsker` transfers finite-block oscillation to Brownian range mass; `FiniteCoverUpper` gives the fixed-cover block estimate; `BlockOscillation` compares the block event with Mogul'skii's source corridor; `QuadraticEnergyCover` supplies the finite `M₃` corridor cover with exponent-two energy; `Rate` assembles the finite-variance rate. The general finite-horizon IID range-to-block inequality now lives at `Path/Block/Partition/Range`. The generic arbitrary-index cover is owned by `Order/Bounds/RangeCover`, and its càdlàg-path adapter by `Topology/Cadlag/Skorokhod/SmallDeviation/RangeCover`. |
| Random-walk entrance and endpoint-corridor estimates | `Probability/Process/RandomWalk/SmallDeviation/Entrance` | `MovingCorridor.lean` owns the moving-boundary event. `NormalDomainEvent.lean` exposes finite entrance events and their membership equivalence; `NormalDomain.lean` owns normal-domain entrance bounds. Finite-variance middle-corridor and endpoint conclusions live under `FiniteVariance/`, with Donsker support under `FiniteVariance/Lemmas/InteriorDiffusive/` and one-use endpoint composition under `FiniteVariance/Lemmas/EndpointBridge.lean`. Under `Robust/`, `Event` and `Measurability` own the central terminal-window event and its prefix measurability; `PowerLower` is the arbitrary-power transition-bound theorem; `FiniteVariance` turns diffusive inverse-square transition bounds into an exponential budget for horizons $L\ge\lfloor\Delta^{2+\varepsilon}\rfloor$. The finite-variance theorem is independent of staircase binning, so it lives with robust entrance estimates; its inverse-square constant extraction remains private. Positive-mass edge-prefix selection and one-use edge geometry are under `Robust/Lemmas/Edge/`. The interfaces cite Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring* (master's thesis, Fudan University, 2026), Appendix A.2, Lemma A.7 and Chapter 3, Lemma 3.5. The finite path, cyclic geometry, and path-ball transfer for the normal-domain entrance proof remain under `Lemmas/Rotation/`; generic finite-product reindex-cover measure transfer and the finite IID survival inequality remain with their general measure and random-walk owners.
| Linearly drifted random-walk tubes and finite-variance bounds | `Probability/Process/RandomWalk/SmallDeviation/DriftedTube` | `Event`, `BlockEvent`, `BlockInclusion`, and `EndpointWindow/` define the moving-tube event, finite-block events, deterministic inclusion, and endpoint-window/reflection correspondence. `FiniteVarianceLower/EndpointBounds` is the source-facing Chapter 3, Lemma 3.5 entry; its staircase-specific construction is contained in `FiniteVarianceLower/Lemmas/Staircase/`. `FiniteVarianceUpper/Basic` is the Chapter 3, Lemma 3.4 entry, with one-use block comparison under `FiniteVarianceUpper/Lemmas/`. The centered finite-variance robust entrance budget shared by both endpoint chains belongs to `SmallDeviation/Entrance/Robust/FiniteVariance`; generic block and horizontal-tube estimates remain with `Path/Block` and `HorizontalTube`. The owner and citations are reviewed, while line-by-line verification of the assembled Lemma 3.5 proof against Wang Yiyang’s thesis remains open.
| Stationary increment laws | `Probability/Process/StationaryIncrements` | `HasStationaryIncrements`; independent of independent-increment and path-regularity assumptions |
| Independent-increment process operations and laws | `Probability/Process/IndepIncrements` | `TimeChange` handles monotone deterministic reparameterizations; `Disjoint` owns separated-increment and disjoint finite-vector independence; `FiniteDimensional` reconstructs position laws and identifies translated process laws; `PathLaw/StationaryTimeChange` identifies centered path laws. The public theorem `FiniteObservations/BlockPaths.lean` extends Mathlib’s single-increment `indepFun_sub_sub` result to arbitrary query families in adjacent blocks; its finite-grid construction details remain private in that module. |
| Expected limits for subadditive random arrays | `Probability/Process/Subadditive` | `Expected` applies Mathlib's scalar Fekete limit to expectations of integrable arrays with mean-stationary increments, almost-everywhere subadditivity, and a linear expected lower bound. It uses no branching or N-selection model. |
| Stable random-walk functional limits | `Probability/Process/RandomWalk/FunctionalLimit/Stable` | `Tightness/Result` proves the three centered-regime tightness criteria; `PathLaw/WalkGrid` and `EndpointGrid` identify finite-grid laws; `PathLaw/Subsequence` and `Process` construct subsequential stable path laws; `PathLaw/Convergence` proves the tightness-plus-grid-law convergence theorem; `PathLimit/RandomWalk` states the three index-regime invariance principles, `PathLimit/Block` handles variable-length blocks, and `Centering` owns the stable-domain truncated-mean bounds and Mogulskii's index-one sine-centering condition |
| Stable random-walk path-law escape rates | `Probability/Process/RandomWalk/FunctionalLimit/Stable/PathLaw` | `Process` constructs a stable clock path law from tight normalized random-walk path laws; `EscapeRate` composes that construction with the stable-process tube-rate transfer, yielding $a^\alpha\log P(\mathrm{tube}(a))\to C<0$ under explicit domain-of-attraction, tightness, and sign hypotheses |
| Finite observation block independence | `Probability/Process/IndepIncrements/FiniteObservations` | `Grid` adapts Mathlib’s `Finset.orderEmbOfFin` to the finite-grid shape used by `HasIndepIncrements`; `BlockVectors` exposes independent finite increment-sum vectors; `BlockPaths` publicly extends Mathlib’s single-increment `indepFun_sub_sub` theorem to arbitrary query families in adjacent blocks; `DisjointPaths` exposes finite-query and path-valued independence. The finite-grid indexing and coordinate projections used in the extension remain private implementation details. |
| Stable-law and stable-process semantics | `Probability/Distributions/Stable` and `Probability/Process/Stable` | Stable distributions and clock-increment/Lévy-process semantics live at their respective owners. `Stable/Basic` defines real-valued measure-level stability predicates; `Stable/CharacteristicFunction/Modulus` owns their characteristic-function modulus consequences; `Stable/Exponent` owns homogeneity and time-additivity of the uniquely represented Lévy–Khintchine exponent; `Stable/Levy` owns existence and uniqueness of that representation. `Stable/Domain/Attraction` and `Stable/Attraction/` combine stable limits with general domain-of-attraction and norming interfaces; the unqualified characteristic-function convergence and regular-variation machinery remain with their generic owners. `Stable/Operations` contains stable-specific closure and convolution-semigroup results; `Stable/Support` contains half-line mass and support properties; `Stable/LevyMeasure/{Scaling,Tail,Cutoff,SignOfJumps}` gives the stable-specific Lévy-triple, homogeneous-tail, finite-variation, and sign-window consequences. Generic cutoff bands and unit-time marked-integrability remain in `MeasureTheory/Measure/Levy/Cutoff` and `Probability/RandomMeasure/Poisson/Intensity/LevyCutoff`. `Process/Stable/Basic`, `Process/Stable/Process`, and `Process/Stable/Levy` layer the stable clock-increment law, càdlàg paths, and identity-clock Lévy specialization over Mathlib's independent-increment API; `Process/Stable/FiniteDimensional` adapts the generic finite-dimensional independent-increment results; fixed-time continuity is proved once for general Lévy processes in `Process/Levy/PathContinuity` from stationary increments and càdlàg paths, and stable clients use `IsStableLevyProcess.toIsLevyProcess`. Mathlib supplies [`HasIndepIncrements`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Process/HasIndepIncrements/Basic.html), [`IdentDistrib`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/IdentDistrib.html), and [finite-dimensional process-law uniqueness](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/FiniteDimensionalLaws.html). `Process/Stable/Brownian` identifies the exponent-two Gaussian case and its canonical unit-interval path law, using Mathlib's Brownian predicates and repository stable-process interfaces |
| Stable-process small-deviation rates and path-class corridors | `Probability/Process/Stable/SmallDeviation/EscapeRate` and `PathClass/StepCorridor` | `EscapeRate/Basic` proves the negative process escape rate; `ConstantCorridorRate` gives the complete fixed constant-corridor rate from stable-clock and stable-Lévy process assumptions; `PathClass/StepCorridor/Rate` transfers the stable escape-rate interface to admissible finite corridors. The generic full-width scalar energy coefficient is defined in `Probability/MeasureTheory/Asymptotics/SmallDeviation.lean`. |
| Stable-process entrance positivity | `Probability/Process/Stable/SmallDeviation/Blocks/Lower/Entrance` | `FullCorridor` gives centered complete-corridor positivity, `PoissonModel` handles finite-variation stable indices, `AllIndices` combines the index regimes into one entrance theorem, `Lower/Entrance/Feedback/{AboveOne,IndexOne}` gives the linear-tube entrance cases, and `PathSupport` transfers corridor positivity to path-law support. `Lower/Feedback/` owns the linear-tube estimates; `ShiftComparison/` consumes entrance positivity in shifted-corridor inequalities. |
| Stable Poisson jump-model endpoint and increment laws | `Probability/Process/Stable/JumpModel` | `EndpointLaw` gives unit-time endpoint and stable time-window laws; `FiniteWindows` gives the joint product law for finite disjoint windows; `IncrementLaw` transfers that law to increments of the selected cutoff path; `IndependentIncrements` proves independent increments and the resulting stable clock-process specification. These are complete interfaces for the canonical finite-variation stable jump construction, not one-use proof stages. |
| Stable-domain norming, characteristic-defect, and tail consequences | `Probability/Distributions/Stable/Attraction/NormingRatios` | `Index` proves norming ratios and divergence; `UniformDefect` and `RegularVariation` transfer attraction to small-frequency defects; `Tauberian` gives tail and truncated-moment consequences. The normalized-sum, first-crossing, and compact-uniform comparison derivations stay local to these result modules; generic regular-variation and Tauberian criteria remain in `Analysis/` |
| Stable-domain norming factors, time scales, and block rescaling | `Probability/Distributions/Stable/Attraction/Norming` | `Basic` defines the truncated-moment factor, stable norming predicate, small-deviation rate, and inverse time scale; `Asymptotics/` owns the consequences for regular variation, centering, norming-scale tails, and block inversion; `Rescaling/` connects domain-of-attraction normalizations to Mogulskii's convention, with the rounded-index construction in `Rescaling/Lemmas/Index`; `SpecialCases/IndexTwo` owns the finite-positive-second-moment norming constructor and index-two normalization results, while `SpecialCases/Gaussian` records the Gaussian truncated-moment limit |
| Gaussian domain of attraction and its truncated-moment consequences | `Probability/Distributions/Stable/Attraction/Normal` | `Basic` owns the finite-variance Gaussian attraction criterion and defect data; `CharacteristicTail` transfers the squared-modulus defect to increment tails; `QuadraticTail` proves Feller's quadratic-tail condition and slow variation for infinite-variance laws; `Centering` proves first-moment integrability and zero mean; `Norming` derives the characteristic-defect comparison, quadratic norming, and tail profiles. Generic discarded-first-moment estimates belong to `Probability/Distributions/Moments/Truncated/TailIntegral`. |
| Real moments, truncated second moments, and tail integrability | `Probability/Distributions/Moments` | `Real.lean` defines the measure-level centered second-moment condition and its scaling, reflection, positivity, and $L^2$ consequences; `Signs.lean` derives half-line mass and bounded increment windows under finite-measure assumptions; `Truncated/Basic` defines and controls the truncated second moment; `Truncated/Layercake`, `TailIntegral`, `TailAsymptotics`, and `RegularVariation` own its tail representations and asymptotic criteria; `TailIntegrability.lean` relates absolute moments and two-sided tails. General regular-variation theorems remain in `Analysis/Asymptotics`. |
| Subadditive ergodic cocycles and their limits | `Probability/Ergodic/Kingman` | `Basic` owns the subadditive-cocycle interface and normalization; `Theorem` is the Kingman convergence entry; `EnvelopeInvariant` exposes the a.e.-invariant liminf envelope; `Derriennic` states the maximal integral inequalities; and `Fekete` gives the normalized-integral limit. Their one-use stopping-time, companion-cocycle, and envelope estimates remain in the module-private `Lemmas/` proof chain. |
| Lévy-process laws and deterministic time shifts | `Probability/Process/Levy` | `Basic` defines the project predicate using a.s. zero start, Mathlib independent increments, stationary increments, and a.s. càdlàg paths; `Shift` proves the recentered process $Y_t=X_{s+t}-X_s$ is again a Lévy process for commutative additive state spaces; `Brownian` adapts Mathlib Brownian motion to this predicate. Mathlib owns the generic [`HasIndepIncrements`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Process/HasIndepIncrements/Basic.html) predicate and Brownian Gaussian characterization; the stationary-increment process package and its shift theorem belong beside the project `IsLevyProcess` definition. |
| Stable Lévy path laws and the Gaussian exponent-two adapter | `Probability/Process/Stable/PathLaw` and `Probability/Process/Stable/Brownian` | `PathLaw/Basic` defines the reusable stable clock-process law on càdlàg paths; `UnitInterval` gives its canonical finite-horizon law; `Concatenation` and `FullProcess` construct the full process from iid unit-interval path blocks; `MonotoneGrid` transfers strict-grid laws to monotone grids, with one-use coordinate calculations under `PathLaw/Lemmas/`; `LinearTube` gives positive mass to Gaussian linear path tubes. `Brownian/{Basic,PathLaw}` connects Mathlib Brownian processes and their increment laws to the exponent-two stable interface. Mathlib supplies `HasIndepIncrements`, the Brownian/Gaussian characterization, `Fin.insertNth`, and finite product-measure reindexing; the stable clock-law predicate and its path-law constructions belong to the stable-process layer. |
| Independence of stable paths on partition cells | `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Partition` | `Independence` exposes mutual independence of the spatially normalized cell paths under the stable clock law; the one-use event-product calculation stays private inside `Partition/Lower/Assembly` |
| Stable-process path-class rates on finite step-corridor partitions | `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor` | `Partition/Core` normalizes each cell under stable time-space scaling and bounds scaled corridor probabilities by products of stable tube probabilities; `Partition/Lower/Kernel` owns complete endpoint-return rate interfaces; `Partition/Lower/Rate` assembles fixed inner-partition lower bounds, with one-use core-shrink and geometry calculations under `Lower/Lemmas/`; `Partition/Upper/EnergyRate` gives the matching energy upper bound and exact `M₂` limit; `Rate` exposes the stable-process `M₂` and `M₃` entries |
| Stable-domain small-deviation blocks and complete-block counts | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Scale` | `BlockLength` owns the stable block length and its scale limits; `BlockCount` exposes the complete-horizon and segment-count limits, specializing the generic quotient/remainder API in `Analysis/Asymptotics/Scale/Block/`; the endpoint-core bridge count and index-one centering transfer stay in `Stable/Discrete/Lemmas/` |
| Stable Mogulskii block corridors and one-block bounds | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Corridor` | owns the stable-length tube events and the source IID block-to-horizon estimates; its closed-range estimate applies the general theorem in `Probability/ConvergenceInDistribution/CadlagPath/RangeOscillation` |
| Power-law small-deviation asymptotics at zero | `Probability/MeasureTheory/Asymptotics` | `HasPowerLawSmallDeviationRate` records eventual positivity and the limit $\varepsilon^\alpha\log p(\varepsilon)\to C$ for any scalar function; `HasStableProcessEscapeRate` specializes it to stable path-tube probabilities in `Stable/SmallDeviation/EscapeRate/PathLaw/Basic` |
| Injective matching with pointwise order domination | `Order/DominatingMap` | `Order.DominatingMap` bundles `f : A → B`, `Set.MapsTo f source target`, `Set.InjOn f source`, and `targetValue (f a) ≤ sourceValue a`. Mathlib provides these set-map and injectivity predicates separately, and `RelEmbedding` preserves and reflects a relation on one carrier; neither bundles this cross-carrier, two-observation inequality. Cloud slice matching specializes this generic structure. |
| Fixed-density transformations of measures | `MeasureTheory/Measure/WithDensity.lean` | `Measure.measurable_withDensity_fixed` proves measurability of the map from a variable base measure to its measure with a fixed measurable density. It complements Mathlib’s `measurable_withDensity`, which fixes the base measure and varies the density; the exponential random-measure tilt uses this parameter-dual result. |
| Lower-tail comparison of measures | `MeasureTheory/Measure/LowerTail` | `Measure.LowerTailDominates μ ν` means $\mu(\operatorname{Iic}(a))\le\nu(\operatorname{Iic}(a))$ at every threshold in any preorder, with no finite-mass or probability assumption. Mathlib’s pointwise measure order and Borel-order uniqueness statements are different interfaces; `Combinatorics/BranchingWalk/Cloud/Order/Slice` specializes this relation to particle Dirac sums and rankwise order. |
| Branching random-walk models, populations, and field coupling | `Probability/BranchingRandomWalk` | `Law.lean` names arbitrary probability laws on walk space; `IID.lean` constructs and transports the canonical product-field law; `Measurability.lean` owns coordinate and finite-survival measurability; `BranchingProperty.lean` gives the selected-subtree law. In `Walk/`, `MeasurableEquiv.lean` identifies singleton-slot walks with their initial positions and optional increments; `Path/` connects this representation to random-walk path laws, finite windows, scaling, and generation-cloud positions; `Rademacher.lean` defines the singleton-slot Rademacher model, and `Path/RademacherFiniteInterval.lean` identifies its finite closed-window event with the killed interval-kernel mass. These are adapters specific to the singleton branching-walk representation; general random-walk path and window APIs remain under `Probability/Process/RandomWalk`. `Population/` owns root-indexed and finite multi-root candidate generation and selected-process recursion; `Restart/RootedTrial/` owns reserve-spine and finite-slot couplings; `Restart/Trial/` owns selected-population split and finite-growth trial interfaces; `Restart/Success/GoodSplit` applies the generic offspring split-mass theorem to a `StepLaw` selector and obtains a finite potential cutoff; almost-sure nonemptiness of the reserve selector remains conditional on the separate offspring nonempty assumption; `Restart/Reserve` owns first-moment estimates for fresh reserve fields; `Restart/Trial/GeometricFirstMoment` specializes the generic IID marked-reward formula from `Probability/Sequence/IID/GeometricReward`. `Restart/RootedTrial/Completion/` owns stopped endpoint laws and causal-source capacity bounds, with proof-only steps under its nested `Lemmas/`. Offspring fields and spine remain at their respective semantic layers |
| Generation branching and additive path-potential decomposition | `Probability/BranchingRandomWalk/Spine/GenerationBranching` | `Decomposition` identifies generation addresses with a first child and a subtree address, gives the root/subtree product law, and states `pathPotential_cons` and the arbitrary-prefix `pathPotential_append` formula; `Measurability` gives joint endpoint-observable and operator measurability; `Recursion` integrates the pathwise decomposition to identify generation observables with iterated branching operators. The prefix/suffix potential identity is part of the path-potential interface, while reserve-spine probability estimates consume it as a dependency. |
| Measurable ordering of random branching-step laws and first-child observations | `Probability/BranchingRandomWalk/Step/Ordering` | `Realization` defines the measurable support-covering ordered realization of one random step; `Field` defines the optional least-slot mark, its node field, and generation measurability; `Law` packages the raw offspring law, potential, and deterministic ordering and transfers point-measure functionals and exponential weights; `Support` gives simultaneous almost-sure ordering, nonemptiness, and first-child survival. Its four modules are complete probability interfaces, not a proof-only chain. Mathlib provides [`Measure.map`, `map_apply`, and `map_map`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Map.html) and [`iIndepFun`/product-law results](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/InfinitePi.html); these supply measure transport and coordinate independence, while child-slot coverage, multiplicity-preserving point measures, and generation-local first-child observations remain specific to branching steps. Whole-tree address transport remains under the deterministic `Combinatorics` layer |
| Finite step-selected branching populations and split-schedule trials | `Probability/BranchingRandomWalk/Population/Processes/StepSelection` | `Basic` owns the recursive selected population and its parent and nonemptiness relations, including the reusable predecessor result from a nonempty successor generation; `SelectedPath` defines edgewise selection and characterizes generation membership by path length and selected edges; `RootIndexed` adds root labels; `Concurrent/{Basic,Scheduled}` groups the global-clock population and its causal-schedule specialization; `SplitSchedule/Definition` owns threshold-triggered trial times and successful root extraction, `Field` owns fresh-pool/product-law and spatial-coupling interfaces, and `Trials` owns completion, iteration, and repeated-success results |
| Abstract branching exploration and stopped subtree laws | `Probability/BranchingRandomWalk/Genealogy/Exploration/Abstract` | `AddressFiltration` defines information generated by address-coordinate fields and generation past/future/descendant independence; `Exploration/` packages inspected domains and countable-range fresh-subtree selection; `JointSubtrees` gives fixed-root product laws; `StoppedPopulation/CellFactorization` and `RandomCardinalityLaw` give fixed-cell and random-cardinality subtree laws; `StoppingSubtree` and `StoppingSubtreeVector/` give scalar/vector stopped versions. The results are mark-generic over `Step α X`; one-use cell partitions and finite enumerations remain private in their theorem modules. The unmarked Galton–Watson model reuses this address-field interface at `X = PUnit`, while the majority of its clients are branching-walk explorations.
| Root-indexed and finite multi-root selected-population candidates | `Probability/BranchingRandomWalk/Population/Candidates` | `Prefix` and `RootIndexed/` define generic address-level child sets; `MultiRoot` and `Adapted` define the finite first-slot candidates and their causal measurability; `Ordering` defines the position/address key directly over `MultiRoot`; `Leftmost` gives fixed-pool ranking and measurability; `FullChildren` and `FullSelection` expose the full-child definitions and finite-to-full selection theorem. The ordered-sibling comparison used only by that theorem is under `Lemmas/FullSelection.lean`. |
| Root-indexed finite first-$N$ population recursion | `Probability/BranchingRandomWalk/Population/Processes/Selected` | `RootIndexed` defines the recursive process, `ParameterizedRootIndexed` gives the joint-measurability interface when the initial position vector is a variable, `Basic` proves adaptation and population bounds, and `GenerationUpdate` states invariance under generation-local field updates. The one-use child-set update identity stays private in `GenerationUpdate.lean`. |
| Causal branching populations and restarted path windows | `Probability/BranchingRandomWalk/Population/Processes/Causal` | `Basic` owns the generation-adapted set-valued population; `RelativePosition/Real` constructs the restarted killed population; `Path/Window` proves both directions between membership and finite path-window conditions. Measurability is a property required by this BRW process construction; the population and path relation remain owned by the branching-random-walk layer. |
| Root-indexed branching-field coupling | `Probability/BranchingRandomWalk/Coupling` | `Slice` links probabilistic couplings to pathwise cloud domination; `Field/Preimage`, `Field/Law`, and `Field/Adaptive` give random matching, fixed pasting, and predictable descendant-field splicing; the optional-preimage measurability argument uses `MeasureTheory/MeasurableSpace/CountableEvaluation` rather than duplicating its generic countable-range evaluation theorem; `Field/Ranked/` owns recursive equal-rank fields, their generation-domain measurability, observable measurability, and product law; its `Lemmas/RecursiveStep` and `Measurability/Lemmas/Past` contain the one-use recursive expansion and past-coordinate proof stages; `Field/Position` specializes to branching-walk positions; `Rank/` owns guarded inverse, generation/block maps, and fixed/adaptive product-law preservation; `Rank/Block/Basic` exposes the block map and structural interfaces, while `Rank/Block/Lemmas/Glue` holds the one-use update identity used by recursive installation |
| Root-indexed branching-field laws, lineages, event counts, and field-level adapters | `Probability/BranchingRandomWalk/Genealogy/RootIndexed` | `Field/` owns the root-address field and generation domain flow; `Law/Basic` owns the root product law and marginals; `Law/RootBatch` maps the root-indexed field to its root-step batch and gives its arbitrary-index product law; `Law/FiniteExpectations` transfers single-root observables to finite root sums; `Law/FiniteRestriction` preserves the law under finite-prefix restriction; `Law/IndependentEventCount` applies the generic finite iid event-count bound to root fields and owns the root-specific exact/exponential avoidance formulas; `Lineage.lean` defines root/trial-indexed reserve paths, their one-generation look-ahead and declared completion times, and stopping-time/measurability results. The distinct one-field interface is `Genealogy/Lineage/PreSampled.lean`; `Field/Selection` adapts first-$N$ ranking to position observations on a root-indexed step field and proves generation measurability |
| Root-indexed step fields, generation filtrations, positions, and adapted observations | `Probability/BranchingRandomWalk/Genealogy/RootIndexed/Field` | `Basic` defines arbitrary-root step-field coordinates and reindexing; `Filtration` uses the generic generated-coordinate filtration to reveal addresses by generation; `Positions` specializes the generic branching displacement to root-dependent initial positions; `Measurability` proves adapted path and selected-position observations and that restriction to a fixed address subtree of depth `s` is measurable by global generation `s + t`; `RelativePosition` gives adapted relative-position results; `Selection` applies the generic measurable ranked-selector API to those observations. Finite-root forms are retained where selected-population clients use them; unused finite-root wrappers were removed in favor of the arbitrary-root statements. |
| Root-indexed address filtrations and fresh-subtree domains | `Probability/BranchingRandomWalk/Genealogy/Exploration/RootIndexed/AddressFiltration` | `PastFuture` owns strict-past/future coordinate independence; `RootSubset` gives coordinate spaces and fresh reserves over arbitrary root sets; `Exploration` specializes disjoint-domain independence to fresh descendants; `GenerationDecomposition` gives the measurable past/future field split and glue map. These are complete root-indexed field interfaces, using Mathlib independence for disjoint coordinate sigma-algebras; local combinatorial address decompositions stay with Ulam–Harris. |
| Fixed and adaptive root-indexed subtree fields | `Probability/BranchingRandomWalk/Genealogy/Exploration/RootIndexed/SelectedSubtrees` | `FixedFamily` owns deterministic reindexing and its future product law; `SelectedFamily` owns the law, event factorization, and independence for generation-measurable root choices; `Iteration`, `Coordinates`, and `Position` track repeated replacements and original locations; `Coupling` compares iterated populations spatially; `GenerationBatch` applies the reusable root-step batch API from `Genealogy/RootIndexed/Law/RootBatch` to generation-selected roots |
| BRW path laws, many-to-one results, path counts, and MRCA decomposition | `Probability/BranchingRandomWalk/Spine/Path` | `ManyToOne/Event` defines one-root history events; `ManyToOne/PathCount` gives path-count/event and moment interfaces; `SecondMoment/Basic` owns pathwise diagonal/off-diagonal and MRCA decompositions, while `SecondMoment/SubtreeLaws` owns distinct-child subtree laws and integrated second-moment identities, independent of corridor geometry and selection |
| BRW affine-tube histories, corridor events, and tube estimates | `Probability/BranchingRandomWalk/Spine/Tube` | Generic affine-corridor events and their deterministic drawdown inclusion are owned by `Probability/Process/RandomWalk/Path/Corridor/Affine`; `Corridor/Drawdown` transfers that pathwise inclusion to the tilted branching-spine increment law. `MRCA/Prefix.lean` owns reusable weighted-prefix factorization and arbitrary measurable corridor continuation estimates; `MRCA/ChildPairBound.lean` exposes the complete fixed-ancestor and integrated cross-child estimates for arbitrary measurable corridors, while its conditional many-to-one and weighted-series calculations remain in `MRCA/Lemmas/ChildPairBound.lean`; the one-use affine-corridor drawdown specialization used by `MRCA/PositiveDepth.lean` is in `MRCA/Lemmas/AffineCorridorContinuation.lean`; `MRCA/PositiveDepth.lean` owns the depth-indexed affine-tube contribution and its finite aggregate, with depth zero covering the root split; `Corridor/PairBound` and `Corridor/SecondMoment` own the corresponding pair and moment estimates |
| General measurable selection mechanisms and adapted populations | `MeasureTheory/Selection` | `Random` defines measurable environment-dependent set-valued and capacity-$N$ rules; `NSelection/` proves measurability of generic ranked-selector extensions at a fixed time; `Finite/` specializes to finite candidates and measurable value rankings; `Causal` and `Finite/Causal` adapt these mechanisms to domain flows; `Process` forms measurable selected-population processes. The underlying `NSelection` structure and deterministic rank rules remain in `Combinatorics/Selection/NSelection`; this subtree contains only their measurable extensions and measurability theorems, not the selection semantics themselves. Stopping-time evaluation is owned by `Probability/Process/Stopping/Selection`. These interfaces quantify over arbitrary candidate types and contain no branching genealogy, offspring, or generation recursion. Mathlib keeps generic finite-set operations under [`Data/Finset`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Defs.html) and measurable structures and functions under [`MeasureTheory/MeasurableSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Basic.html); the project selector APIs are organized by those mathematical objects, with branching semantics added only in the branching-walk layer. |
| Branching-random-walk selection applications | `Probability/BranchingRandomWalk/Selection` | `Finite/RootIndexed` adapts measurable value selection to root-indexed particles; `Overflow` defines capacity-exceedance generations and stopping-time results; `Coupling/Basic` transfers deterministic cloud domination to causal finite selections; `Coupling/SelectedPopulation` instantiates the arbitrary-offspring pathwise coupling for the causal first-$N$ population on a pre-sampled root-indexed field; `Coupling/StepSelection` specializes it to labelled step-selected trials. The generic first-$N$ selector and arbitrary-offspring induction remain in `Combinatorics/BranchingWalk`; `NSelection/` owns the BRW selected-population laws, speeds, and deviation estimates. |
| Deterministic first-`N` selection, speed, and tail estimates | `Probability/BranchingRandomWalk/Selection/NSelection` | `Admissible/Real.lean` proves almost-sure lower-finiteness and first-`N` specifications for populations generated from a root-indexed branching-random-walk field; `Law/SelectedPopulation.lean` owns the selected-population law. `AsymptoticSpeed/` contains the environment-law and speed arguments, while `EndpointDeviation/` contains the endpoint and drawdown estimates. The generic ranked selector and its fixed-time measurability theorems live under `Combinatorics/Selection/NSelection` and `MeasureTheory/Selection/NSelection`; the deterministic offspring recursion lives under `Combinatorics/BranchingWalk/Selection/NSelection/Walk`. This probability subtree contains the branching-random-walk laws and estimates built from those interfaces. The stopping-time rank-vector selector is in `Probability/Process/Stopping/Selection/Ranked.lean`; it applies the generic ranked selector to an arbitrary time-indexed candidate process and proves stopped measurability. Position-based measurability on root-indexed fields is placed with `Genealogy/RootIndexed/Field/Selection`. `AsymptoticSpeed/Environment/Basic` defines the generation batches, product environment law, shift invariance, and generation-coordinate domains, with marginal, independence, and almost-sure good-transition interfaces; `Environment/ErgodicEnvironment` specializes `ProbabilityTheory.iidSequenceShift_ergodic` to that law; `Environment/OrderDual` transports the batch and environment laws through the generic step `OrderDual` map. `AsymptoticSpeed/Selection/PopulationBatch` enumerates the selected generation by spatial rank and proves that offspring batches read at those roots are independent with the iid generation-environment law. The remaining subtree owns selected-population endpoint/drawdown bounds and speed proofs. `Law/SelectedPopulation.lean` is the product-law interface for the totalized first-`N` target; `Law/Causal/` groups the causal-population, arbitrary causal-selection, step-selection, restarted-window, and nested-root coupling specializations. `EndpointDeviation/Endpoint/Minimum/{Basic,Address,CountableRoots}` owns the totalized minimum, its canonical measurable minimizing address, and the countable-root pushforward-law identity; the one-use predictable-lineage fourth-moment proof is grouped under `Endpoint/Minimum/Lemmas/`. Under `EndpointDeviation/FirstStage/`, `Cutoff.lean` defines the logarithmic first-stage cutoff and its scale properties; the positive tilted-spine corridor specialization used in the PZ proof is under `FirstStage/Lemmas/CorridorLowerBound.lean`. `Population/RestartedWindow.lean` owns the two-stage drift and window schedule; the one-use successful-root embedding proof is under `Population/Lemmas/Embedding.lean`. `Drawdown/Spine/` is reserved for the drawdown-dependent killed-capacity estimates, and its `Lemmas/` contains their theorem-specific reductions. Under `EndpointDeviation/SecondStage/`, `Tube.lean` owns the affine tube, all-root failure event, and one-root PZ ratio; `Population.lean` owns the restarted killed population and finite-slice theorem; `Roots/Population.lean` owns the restarted field/population types and threshold event; `Roots/Selection.lean` owns the predictable finite-slice root constructor and its measurable, injective-family interface. The one-use pathwise population transfer is in `Lemmas/PopulationTransfer.lean`; the predictable-root probability estimate and its finite-slice specialization form one proof chain in `Roots/Lemmas/AllAvoid.lean`. |

Directory names should follow the owning concept. A declaration is not moved
to a theorem-specific directory merely because that theorem currently uses it.
Conversely, a general-looking name does not justify a generic module if its
definition relies on stable, branching, or other model-specific hypotheses.
The word `Selection` does not determine module ownership by itself. The generic
`Combinatorics.Selection.NSelection ι N` acts on arbitrary candidate sets:
`M.select : Set ι → Finset ι`, with `M.select s ⊆ s`, cardinality
`min N (s.toFinset.card)` when `s` is finite, and cardinality `N` when `s` is
infinite. It has no branching-step data. In contrast,
`Combinatorics.Branching.Step.FiniteSelection α X` assigns each step `ξ` a finite
set of slots contained in `support ξ`; its slot-order and potential rules
belong in `Combinatorics/BranchingWalk/Step/Selection`. Measurability of the
generic selector belongs in `MeasureTheory/Selection`, while measurability of
the branching-step selector belongs in
`MeasureTheory/BranchingWalk/Step/Selection`. Generation-wise selected
populations belong in `Combinatorics/BranchingWalk/Selection`, and their
probability laws and stochastic estimates belong in
`Probability/BranchingRandomWalk/Selection`.

This is a semantic boundary, not a placement of all objects named
`Selection` under one parent. `NSelection` is a deterministic finite-capacity
subselector on arbitrary sets; its defining module uses set and cardinality
interfaces and has no `MeasurableSpace`, probability, offspring, or genealogy
parameter. It therefore belongs to the generic combinatorial layer. Measure
Theory proves properties of this operation when its inputs vary measurably;
BranchingWalk owns two distinct specializations: `Step.FiniteSelection` selects
child slots from one branching step, while `RootIndexed.NSelection` transforms
an entire branching walk into one with at most `N` surviving children at each
node. Neither branching-specific object is the generic candidate-set
`NSelection`, and neither belongs in `MeasureTheory/Selection`.

The generic owner is supported by clients whose statements range over
arbitrary candidate types and time-indexed finite candidate sets, including
`MeasureTheory/Selection/NSelection` and
`Probability/Process/Stopping/Selection/Ranked`. The latter states its
selector and stopped-rank results without offspring or genealogy assumptions.
This makes `Combinatorics/Selection` a reusable finite-candidate interface,
while `Combinatorics/BranchingWalk/Step/Selection` remains the owner of
selection whose candidates are child slots of a branching step. Mathlib's
generic finite-set ordering is under `Data/Finset`, whereas graph-walk
construction is under `Combinatorics/SimpleGraph/Walk`; this follows the same
split between general finite-candidate operations and a model-specific walk.
The closest Mathlib selection precedents checked are `Finset.rado_selection`
in `Combinatorics/Compactness`, which combines choices indexed by finite sets
into a global choice compatible with larger finite sets, and Hall's theorem
in `Combinatorics/Hall`, which selects
distinct representatives from finite candidate sets. They have different
statements from a selector of capacity $N$, but confirm that finite-candidate
selection and matching belong to the combinatorial layer. The project
interface remains distinct because it specifies
$M:\mathcal P(\iota)\to\operatorname{Finset}(\iota)$,
$M(S)\subseteq S$, and
$|M(S)|=\min(N,|S|)$ for finite $S$, with $|M(S)|=N$ for infinite
$S$. The comparison was checked against the pinned Mathlib revision
`380f2aafb622cb2c1c93dac545b6389083c68c51` and its
[official API documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Compactness.html)
and [Hall API documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Hall/Basic.html).

Thus measurable hypotheses do not make `NSelection` a `MeasurableSpace`
object: `MeasureTheory/Selection/NSelection` contains measurable theorems about
the generic definition in `Combinatorics/Selection/NSelection`, while the
branching-step measurable adapters live beside the branching-step object.

## Mathlib reuse

- Measures and point masses use `Measure`, `Measure.dirac`, and Mathlib's
  measure operations. `Measure.iOptionDiracSum` adapts a family of optional
  atoms to a measure sum; it does not introduce another measure type.
- Optional values use the measurable-space instance and complete measurability
  API in `MeasureTheory/MeasurableSpace/Option.lean`. At pinned Mathlib
  revision `380f2aafb622cb2c1c93dac545b6389083c68c51`,
  `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean` supplies the
  disjoint-union measurable structure on `Sum` and its measurable injections,
  but the pinned `Mathlib/MeasureTheory/MeasurableSpace/` tree has no matching
  `Option` instance. The local instance is induced by `some : X → Option X`,
  giving the standard disjoint-union structure with a measurable `none`
  singleton. Its operations are named in the `MeasureTheory` namespace, which
  is the semantic owner; branching-step clients consume this API without
  redefining the optional measurable structure.
- Mathlib's `Mathlib.MeasureTheory.MeasurableSpace.Constructions` provides
  `measurable_finset_iff`, the membership-event characterization for
  measurable finite-set-valued maps. Its pinned API has no pointwise,
  parameter-dependent finite-set filter theorem, so
  `MeasureTheory/MeasurableSpace/Finset/Filter.lean` supplies the general
  result `Measurable.finset_filter`; branching-step filtering is its
  specialization.
- The pinned Mathlib revision
  `380f2aafb622cb2c1c93dac545b6389083c68c51` supplies the general ENNReal
  product and sum reindexing operations, including `ENNReal.tsum_prod` and
  `ENNReal.tsum_add`, but not the arbitrary-weight diagonal/off-diagonal
  partition of a countable pair sum. That decomposition is stated in
  `Topology/Algebra/InfiniteSum/ENNReal/PairPartition.lean`; its statement has
  no branching or probability assumptions, so branching clients import it
  instead of defining a specialized generic sum lemma.
- `MeasureTheory/Measure/Finite/OnFamily.lean` defines
  `IsFiniteOnFamily ν 𝒜 := ∀ s ∈ 𝒜, ν s ≠ ∞`; `Finite/Domination.lean` proves
  the general a.e.-finiteness consequence of an integrable bound
  `ν ω s ≤ C s * W ω`. The latter has no client-specific assumptions and is a
  complete result for random measure-valued families, so it is a public peer
  module under `Finite/`, not a helper in a proof-only `Lemmas/` directory.
  The pinned Mathlib APIs used are `ae_lt_top'` and the integral bound in
  `Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean` at pinned revision
  `380f2aafb622cb2c1c93dac545b6389083c68c51`; the [official API documentation]
  (https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.html)
  describes these Markov and a.e.-finiteness results. A repository-wide search
  of the pinned `Mathlib/MeasureTheory/Measure/` sources found no theorem
  combining them into simultaneous finiteness on a countable family.
- `Finite/OnFamily.lean` also exposes `leftRayFamily` and `rightRayFamily`.
  The π-system facts for these ranges are already exactly Mathlib's
  `isPiSystem_Iic` and `isPiSystem_Ici`, so the former local forwarding
  wrappers were removed. `mem_rightRayFamily_iff_orderDual` remains because
  it relates the repository's two family definitions by order duality.
- The pinned Mathlib tightness API provides singleton tightness and closure
  under finite unions, but no finite-image theorem for an arbitrary index set.
  `Measure/Tight/FiniteFamily.lean` supplies that generic induction principle;
  both the sequence-prefix theorem and the random-walk finite-family result
  now reuse it. See the [Mathlib tightness API]
  (https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Tight.html)
  and [π-system API]
  (https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/PiSystem.html).
- The local `PointProcess` bundles Mathlib measures with the measurability,
  integer-valuedness, and finite-on-family properties required of a random
  counting measure. Its branching-step adapter stays in the branching-random-
  walk layer.
- Countable independent product laws use `Measure.infinitePi` and the
  `iIndepFun` results in Mathlib. `iidSequenceLaw` names the homogeneous
  sequence specialization used throughout the library. Generic finite block
  coordinates, their measurability, and the measurable `Function.extend Fin.val`
  map for finite blocks belong to `Probability/Sequence/Block`;
  the law of every such block and the probability of a measurable block event
  belong to `Probability/Sequence/IID/Basic`. These interfaces require only an
  IID sequence law and do not belong in random-walk entrance or stopping-time
  modules. Stopping-time-specific factorization stays in
  `Probability/Sequence/IID/Blocks/StoppingTime`.
- Transition mechanisms use Mathlib's `Kernel`/`MarkovKernel` interfaces.
  Killed kernels in the random-walk layer are restrictions of those kernels.
- `Probability/Kernel/Survival/` builds finite return and bridge operations
  from Mathlib's kernel powers, composition, and `Kernel.comapRight`. The
  local API keeps the unrestricted kernel and restricts initial and terminal
  states through measurable subtypes; its block estimates are stated for
  arbitrary kernels and sets rather than a particular random-walk model.
- Mathlib's `HasIndepIncrements` is defined for a process over a preorder and
  only records independence of consecutive increments. It does not include
  stationary increment laws. `Probability/Process/StationaryIncrements/Basic`
  defines that separate law identity on an additive time monoid. The
  finite-dimensional law results combine both properties only where their
  conclusions require them; Lévy path regularity stays in `Levy`.
- `Probability/Independence/ConditionalIntegral.lean` relates independent
  random variables to Mathlib's regular conditional distribution API. In
  particular, if $X$ and $Y$ are independent and $E$ is measurable, then
  $\mathbb E[\mathbf1_E(X,Y)\mid X](\omega)$ equals the $Y$-marginal
  probability of the section $\{y:(X(\omega),y)\in E\}$. Consecutive IID
  block applications obtain independence from
  `Probability/Sequence/IID/Blocks/StoppingTime.lean`.
- Filtrations and stopping times use Mathlib's `Filtration` and stopping-time
  predicates. Process-specific adaptedness proofs are adapters from the
  process maps to those interfaces.
- `Probability/Process/Filtration/GeneratedByCoordinates.lean` defines the
  least filtration generated by arbitrary measurable observations with grades
  in an arbitrary preorder; its dependent observation spaces and iff
  criterion for measurability into each generated σ-algebra are shared
  process infrastructure.
- `Probability/Process/Filtration/ConditionalBlocks.lean` gives finite product
  bounds for arbitrary event sequences from conditional indicator bounds.
  Its probability normalization is part of the unscaled product statement;
  random-walk-specific block events remain in their small-deviation modules.
- Finite observation and time-threshold selection use Mathlib's generic
  `MeasureTheory.hittingBtwn`. `Probability/Process/TimeGrid/Ceiling.lean`
  names the time-functional threshold specialization and proves the grid
  convergence properties that Mathlib's first-hit interface does not supply.
  This boundary was checked against the pinned source in
  `Vendor/Mathlib/Mathlib/Probability/Process/HittingTime.lean` and the
  [official Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/HittingTime.html):
  `hittingBtwn` already handles the first entry of an arbitrary indexed process
  into an arbitrary set on a bounded ordered time interval. The local API
  therefore stays a threshold specialization over an arbitrary domain and
  contributes only the ceiling-specific convergence and measurability facts;
  path and Brownian-law assumptions remain in their owning modules.
- `Topology/Order/NNReal/Rational.lean` owns the dense-range theorem for
  the canonical coercion $\mathbb Q_{\ge 0}\to\mathbb R_{\ge 0}$ and its
  interval-selection consequence. These are topological/order facts used by
  continuous-path arguments; the countable dense set is independent of the
  probability-process time-grid constructions. The pinned Mathlib library
  provides rational density in archimedean ordered fields, while this file
  adapts it to the nonnegative subtype.
- `Order/Interval/UniformGrid` is the affine-grid interface for ordered
  fields. Process-time grids use `ℝ≥0`, so they are not direct instances of
  that structure; moreover, the process-time modules need horizon and mesh
  density results that the affine-grid interface does not state. Keep those
  time coordinates in the `Probability/Process/TimeGrid` owner instead of
  adding a real-valued conversion layer solely to reuse the structure.
- Càdlàg paths and Skorokhod-space constructions reuse the path-space objects
  supplied by the project dependencies. Local criteria add the estimates and
  interfaces needed by this library's limit theorems.
- The pinned Mathlib
  [`Topology.MetricSpace.ShrinkingLemma`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/ShrinkingLemma.html)
  shrinks locally
  finite covers by open balls in proper metric spaces, while
  [`Topology.Neighborhoods.nhds_basis_opens`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Neighborhoods.html)
  expresses neighborhood bases. The pinned source files are
  `Vendor/Mathlib/Mathlib/Topology/MetricSpace/ShrinkingLemma.lean` and
  `Vendor/Mathlib/Mathlib/Topology/Neighborhoods.lean`.
  Neither gives the finite ordered core radii required by a step-boundary
  partition: the first has cover/properness hypotheses and a cover-preserving
  conclusion, and the second carries no indexed radius-growth condition. The
  step-corridor geometry therefore stays public at its path-topology owner.
  Its single-call scalar-contraction proof is theorem-specific and belongs in
  the stable partition proof's `Lemmas/` subtree; this audit adds no parallel
  generic radius-selection API.
- Finite affine grids are represented by `UniformGrid` with caller-supplied
  endpoints. Rational and dyadic grids provide arithmetic specializations.
  Mathlib's `Dyadic` and additive subgroups remain the right objects for
  unbounded dyadic coordinates and additive lattices, respectively.

When a local definition wraps one of these objects, its module should state
what extra semantics it supplies and keep the map to the underlying Mathlib
object explicit.

## Placement checks for new definitions

Cross-module use is evidence that an object deserves review, not evidence that
it belongs at a higher layer. The number of clients does not determine the
right abstraction. Every proposed promotion or outward move therefore triggers
an online abstraction search: inspect official Mathlib documentation and
source, the pinned dependency APIs, and relevant mathematical literature where
it can reveal a broader statement. Compare the exact hypotheses and
conclusions, not just names. A public object should state the mathematical
structure or result with the weakest natural assumptions that its proof
supports; a single-use proof step stays private or under the owning module's
`Lemmas/` subtree. Generalize the local API when the broader statement has
independent mathematical meaning and can be proved without importing the
application that currently uses it. Record the sources, the closest general
form, its hypotheses, and why it does or does not subsume the local result in
this file or the directory audit; include the checked dependency revision.
This check follows Mathlib's official
[review guidance](https://leanprover-community.github.io/contribute/pr-review.html#location-location),
which asks whether a result already exists in a more general form and whether
the literature provides a more general statement using existing library
concepts.

For each public object, answer these questions in review:

1. What is the mathematical data, independently of the theorem using it?
2. Does Mathlib already provide that data or a theorem with the same scope?
3. What is the weakest set of assumptions needed to define it?
4. Which lower layer owns those assumptions and operations?
5. What more general form is available in Mathlib, dependencies, or the
   literature, and how do its hypotheses compare?
6. Is this a genuine specialization/adapter, or an unnecessary parallel API?
7. If it is a specialization, does it provide a complete result with an
   independent mathematical use, or only one proof-chain step?

When the existing source does not resolve the abstraction question, inspect
the official Mathlib documentation/source and relevant references online. Check
any candidate against the repository's pinned dependency, compare its exact
assumptions and semantics with this statement, and record why the local public
interface is still needed. Cross-module use is an audit trigger; mathematical
generality, the strongest sound candidate interface, and the content added by
the theorem determine whether to expose it and where to place it.

Keep a model-specific assumption at the application boundary. For example,
the definition of a generic measurable path should not assume a stable law,
and a deterministic child step should not assume that a child exists or that
its slots are ordered.

## Brownian modification and diffusive tube ownership review (2026-10-22)

This review compared the candidate abstractions with Mathlib's official
[`IsBrownianReal` API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/BrownianMotion/Basic.html),
its [continuous-path Borel API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousMap.html),
and Mathlib's [module-placement review guidance](https://leanprover-community.github.io/contribute/pr-review.html).
The checks were repeated against the pinned Mathlib revision
`380f2aafb622cb2c1c93dac545b6389083c68c51` and BrownianMotion revision
`d6d901b6df592a543b7edf221f92d2ee6760d18d`.

Mathlib defines `IsBrownianReal` by Brownian finite-dimensional laws and
almost-sure path continuity; `IsPreBrownianReal` supplies the finite-dimensional
laws without the path-continuity condition. Under its stated topological
hypotheses, the Borel σ-algebra on continuous maps is generated by coordinate
evaluations. The BrownianMotion dependency supplies the general
Kolmogorov--Chentsov modification theorem
[`exists_modification_holder'`](https://github.com/RemyDegenne/brownian-motion/blob/master/BrownianMotion/Continuity/KolmogorovChentsov.lean).
The local `IsPreBrownianReal.continuousModification` specializes this theorem
to Brownian fourth moments. High-level Brownian corridor and Donsker comparison
results consequently need only the standard `IsBrownianReal` assumption. The
lower-level step-path limit still takes a specified measurable continuous
path representative because its conclusion is the law of that exact path
map. No second generic continuous-path representation is introduced.

The same dependency revision also contains the higher-level
`IsPreBrownianReal.exists_continuous_modification` and `IsPreBrownianReal.mk`
in `BrownianMotion/Gaussian/BrownianMotion.lean` (pinned source:
[`d6d901b`](https://github.com/RemyDegenne/brownian-motion/blob/d6d901b6df592a543b7edf221f92d2ee6760d18d/BrownianMotion/Gaussian/BrownianMotion.lean)).
That construction uses the Gaussian moment bounds for every natural exponent,
so it subsumes the local fixed-fourth-moment route mathematically. Importing
that module in this checkout currently triggers dependency build failures in
`KolmogorovExtension4.KolmogorovExtension` and
`BrownianMotion.Gaussian.Moment`; the local adapter instead imports the
buildable general `exists_modification_holder'` interface and uses the fourth
moment, which already suffices for path continuity. Keep this smaller route
until the pinned dependency chain builds; revisit the promotion after that
compatibility issue is repaired. This comparison does not justify a second
general continuous-path construction.

The exact Donsker estimates for a centered unit-variance walk in a horizontal
tube have no Mogulskii-scale assumption: for example, their hypotheses are
only `IsCenteredUnitSecondMoment ν`, a Brownian inner/outer width comparison,
and the diffusive width `w * sqrt n`. They are complete lower-bound results,
so they now live at the random-walk small-deviation owner in
`HorizontalTube/Diffusive/TubeLower.lean` and
`HorizontalTube/Diffusive/EndpointLower.lean`. Generic finite-time IID block
comparisons for horizontal tubes are in `HorizontalTube/Blocks/UpperBound.lean`;
the strict whole-path IID range bound is in
`Path/Block/Partition/Range.lean`.
Mogulskii-specific seven-window endpoint-band estimates and finite-partition
gluing remain under `Mogulskii/Lemmas/EndpointBands/` and
`Mogulskii/Lemmas/Partition/`; the stable discrete partition-rate interfaces
remain under `Mogulskii/Stable/Discrete/Partition/`.
The finite-state principal-mode estimate remains under the Rademacher
finite-interval owner, and the real cosine-logarithm limit remains under
`Analysis/SpecialFunctions/Trigonometric/LogAsymptotics.lean`.

Variable-width upper and lower log-rate estimates, endpoint-prefactor limits,
interior-start limits, and centered-tube limits use only the killed
finite-interval Rademacher kernel. They are grouped under
`Rademacher/FiniteInterval/Spectral/Survival/Asymptotics/`. The sole
arbitrary-real-width result,
`tendsto_scaledLog_centeredHorizontalTubeProbability_of_realScale`, lives in
that Rademacher module because it assumes only divergence of the real width,
positive integer times, and a vanishing squared-width/time ratio. The
Mogulskii `Scale/CenteredTube.lean` wrapper has been removed; its two-use
specialization stays private in `Mogulskii/Gaussian/EscapeConstant.lean`.

The killed return-kernel consequences of these Donsker corridor estimates
also have no Mogulskii-scale hypothesis. Their complete probability bounds
belong in `HorizontalTube/Kernel/DiffusiveReturnLower.lean`. A separate adapter that sampled
this estimate at the scale's rounded diffusive block length had no clients and
was removed. The finite horizontal-block comparisons depend only on IID
increments, so they are owned by `HorizontalTube/Blocks/UpperBound.lean`; the
strict IID range-event counterpart is in
`Path/Block/Partition/Range.lean`. The diffusive target-mass
limit uses the finite-state Rademacher sine spectrum and belongs
in `Rademacher/FiniteInterval/Spectral/Target/DiffusiveLower.lean`, beside
the finite-time target-mass estimate. These modules contain complete
mathematical results, so their standalone file placement records their
semantic interfaces; short proof steps remain private in their callers.

The public endpoint-window event and its normalized form are owned by
`HorizontalTube/EndpointWindow/Basic.lean`; the finite-family Portmanteau
transfer and its seven-window tube consequence are in
`HorizontalTube/EndpointWindow/PathLawTransfer.lean`. The integer-width
finite-variance bound and its real-width extension are siblings in the same directory. The
two Donsker lower bounds are grouped under `HorizontalTube/Diffusive/`, while
the uniform killed-kernel iteration and diffusive return estimate are grouped
under `HorizontalTube/Kernel/`. This keeps the subject root small while each
subdirectory names the estimate's mathematical role. These are complete
probability interfaces, so they remain public outside `Lemmas/`.

The placement decision follows Mathlib's review questions: compare the exact
hypotheses, move complete general results to their semantic owner, and keep
only application-specific assembly in the theorem's subtree. Cross-module use
triggered this review but did not itself justify the promotion.

## Abstraction review: process scaling and first-block return laws (2026-10-19)

The mathematical abstraction investigated is $H$-self-similarity: for every
positive time scale $c$, every finite family of times $t_1,\ldots,t_n$,
and exponent $H$,
\[
  (X_{ct_1},\ldots,X_{ct_n})\overset d=
  (c^H X_{t_1},\ldots,c^H X_{t_n}).
\]
This is the finite-dimensional-distribution definition of self-similarity;
see John Lamperti, “Semi-stable stochastic processes,” *Transactions of the
American Mathematical Society* 104(1) (1962), 62--78,
[DOI 10.1090/S0002-9947-1962-0138128-7](https://doi.org/10.1090/S0002-9947-1962-0138128-7).
Stable Lévy scaling has $H=1/\alpha$, while Brownian scaling has $H=1/2$.

The checked Mathlib revision is
`380f2aafb622cb2c1c93dac545b6389083c68c51`. Its
[`FiniteDimensionalLaws`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/FiniteDimensionalLaws.html)
API proves that equality in law of processes is characterized by equality
of every finite-dimensional distribution. The pinned source is
`Vendor/Mathlib/Mathlib/Probability/Process/FiniteDimensionalLaws.lean`,
including `identDistrib_iff_forall_finset_identDistrib`. No self-similarity
predicate or stable/Brownian scaling theorem is supplied by that API.

The repository has two model-specific realizations of the literature's
scaling relation. `IsStableLevyProcess.timeSpaceScale_positions_identDistrib`
in `Probability/Process/Stable/FiniteDimensional.lean` identifies the
finite-position laws on monotone grids, and
`IsBrownianReal.measure_continuousPathMap_scale_eq` in
`Probability/Process/Brownian/PathLaw/ContinuousPathLaw.lean` identifies the
law on continuous path space under
\(f(t)\mapsto c^{-1/2}f(ct)\). Their common finite-dimensional content is a
candidate for a public self-similarity interface if it can serve both model
families without adding a thin wrapper around `IdentDistrib`. The current
interfaces retain the stronger structure each proof uses: stable increment
specifications for the first and continuous path laws for the second.
This audit does not add an `IsSelfSimilarProcess` predicate: the current
proofs consume finite-dimensional `IdentDistrib` for stable processes and a
full continuous-path law for Brownian motion, while such a predicate would
only package the former relation without providing a shared path-law theorem.
Revisit it when a model-independent theorem can consume the same hypothesis
in both settings.

For the lower-block return estimate, the exact general candidate is already
available as
`IsStableLevyProcess.corridorReturn_timeSpaceScale_inv`: for every horizon
\(h>0\),
\[
  \mathbb P(X_{h\cdot}-X_0\in\mathcal C(l,u,c_-,c_+))=
  \mathbb P(X_{\cdot}-X_0\in
    \mathcal C(h^{-1/\alpha}l,h^{-1/\alpha}u,
      h^{-1/\alpha}c_-,h^{-1/\alpha}c_+)).
\]
It is used by the entrance-scaling proof and lower-block bounds. The two
lower-block callers need only its first-uniform-block instance, where
\(h=1/N\). `firstBlock_corridorReturn_scale_inv` is therefore retained under
`Blocks/Lower/Lemmas/` as a supporting lemma, derived from the arbitrary-
horizon theorem and the first-block path identity. The broader scaling
operation remains at `Blocks/ReturnScale.lean`; client count does not promote
the adapter. This audit records the H-self-similar candidate separately so
future scaling results can be reviewed against it before adding another
public abstraction.

## Reuse audit: drawdown prefix maxima (2026-10-19)

The Drawdown proof had defined
\[
  M_n(f)=\max_{0\le j\le n}f(j)
       =(\operatorname{range}(n+1)).\operatorname{sup'}(f).
\]
The pinned Mathlib API already provides the more general partial supremum
`partialSups f n`, defined for a locally finite ordered index with bottom and
a target semilattice supremum. Its natural-number specialization satisfies
`partialSups_eq_sup'_range`, so the local `prefixMaximum` had exactly the same
meaning and assumptions were strictly narrower. The same API supplies
`le_partialSups_of_le`, `partialSups_le`, and `partialSups_monotone`, covering
the local pointwise, upper-bound, and monotonicity lemmas.

This was checked against pinned Mathlib revision
`380f2aafb622cb2c1c93dac545b6389083c68c51`, specifically
`Vendor/Mathlib/Mathlib/Order/PartialSups.lean` and the official
[`Mathlib.Order.PartialSups` documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/PartialSups.html).
The Drawdown modules now use `partialSups` directly. The floor-rounded
`spatialBinIndex`, `spatialBinLevel`, and the constant-bin and jump-pattern
conclusions stay in `Drawdown/FiniteVarianceUpper/Lemmas/JumpPattern/`, since
their statements depend on this proof's upper boundary, bin width, and
drawdown event. The proof-specific translation identity in
`ConditionalBlocks.lean` is expressed through Mathlib's
`partialSups_eq_sup'_range`; no second running-maximum abstraction remains.

## Brownian modification and finite-interval spectral ownership review (2026-10-22)

The online abstraction search compared Mathlib's Brownian predicates and
continuous-path Borel structure with the pinned BrownianMotion dependency and
the local Donsker and small-deviation interfaces. Mathlib's official
[`IsBrownianReal` documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/BrownianMotion/Basic.html)
defines Brownian motion as a process with Brownian finite-dimensional laws and
almost-surely continuous paths. The same API gives only `AEMeasurable` for a
pre-Brownian coordinate. Mathlib's official
[`ContinuousMap` Borel documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousMap.html)
states that, under its second-countability and local-compactness hypotheses,
measurability into continuous-path space is characterized by measurable
coordinate evaluations. These statements were checked against the pinned
Mathlib revision `380f2aafb622cb2c1c93dac545b6389083c68c51` in
`Vendor/Mathlib/Mathlib/Probability/BrownianMotion/Basic.lean` and
`Vendor/Mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousMap.lean`.

The pinned BrownianMotion dependency, revision
`d6d901b6df592a543b7edf221f92d2ee6760d18d`, supplies the general
Kolmogorov--Chentsov modification theorem
`exists_modification_holder'` in
`Vendor/BrownianMotion/BrownianMotion/Continuity/KolmogorovChentsov.lean`;
its upstream source is the
[BrownianMotion formalization](https://github.com/RemyDegenne/brownian-motion/blob/master/BrownianMotion/Continuity/KolmogorovChentsov.lean).
The local `Brownian/Construction/PreBrownianModification.lean` specializes
that theorem to Brownian fourth moments and exposes a measurable,
everywhere-continuous modification. This local constructor bridges Mathlib's
standard `IsBrownianReal` assumptions to the path-space Donsker API without
adding coordinate measurability or everywhere-continuity hypotheses to the
public theorem. Accordingly, `Donsker/Path/Skorokhod.lean` and the Brownian
corridor comparison modules use the selected local modification. The
high-level corridor comparison accepts `IsBrownianReal` alone. The lower-level
path-space Donsker theorem keeps the explicit measurable, everywhere-continuous
representative in its hypotheses because its conclusion names that exact
path-valued map. The continuous-path Borel construction is not duplicated;
the local adapter supplies the modification that the existing Kolmogorov
theorem does not package as a Brownian-process API.

The exact quantitative Brownian corridor lower bound has no matching Mathlib
theorem. It remains at `Probability/Process/Brownian/SmallDeviation/`, where
its statement is about Brownian corridor probability and its proof transfers
the discrete Rademacher spectral estimate through Donsker--Portmanteau. The
killed finite-interval survival estimate and its diffusive spectral limit
were moved to `Probability/Process/RandomWalk/Rademacher/FiniteInterval/`:
they are statements about the centered finite-state walk and no longer import
Mogulskii. The rounded centered lattice radius belongs beside that finite
interval model because it selects its state interval from a real scale. The
pure real-variable limit for `x^2 log(cos(π/x))` belongs to
`Analysis/SpecialFunctions/Trigonometric/LogAsymptotics.lean` and reuses
Mathlib's logarithmic cosine asymptotic. This separation follows mathematical
ownership, not the current list of Mogulskii callers.

## Finite integer-family range translation (2026-10-22)

The former `Mogulskii/Spectral/Range/Basic.lean` mixed the Rademacher path's
integer-coordinate representation with the Mogulskii finite-cover estimate.
The path-specific declarations now live in
`Probability/Process/RandomWalk/Rademacher/FiniteInterval/Range/Basic.lean`.
The translation step is stated in the broader form
`Order.Bounds.exists_int_translate_into_Icc_of_pairwise_dist_le`: for a
finite nonempty index type $I$ and $x:I\to\mathbb Z$, if
$|x_i-x_j|\leq w$ for all $i,j$, then some $c\in\mathbb Z$ satisfies
$c+x_i\in[0,w]$ for every $i$. This requires only finite integer data and
the pairwise-diameter bound, so it applies to any integer-valued finite path;
the Boolean Rademacher encoding is absent from the public statement. The
Rademacher-only conversion from real partial sums to this integer theorem is
private in `Probability/Process/RandomWalk/Rademacher/FiniteInterval/Range/Probability.lean`.

The online Mathlib comparison used the official
[`Finset.exists_min_image` API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Max.html),
the [integer interval API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Int/Interval.html),
and the [general interval API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Interval/Basic.html).
These provide finite extrema, integer interval enumeration, and interval
structures, respectively; the checked pages do not provide the finite-family
translation conclusion. The same check against pinned Mathlib revision
`380f2aafb622cb2c1c93dac545b6389083c68c51` found no matching range-translation
theorem. The local result therefore adds a model-independent finite
integer-family fact using the existing minimum API rather than a
Rademacher-specific public helper.

## Cosine-power asymptotic ownership review (2026-10-22)

The online Mathlib comparison found its general power and filter-limit
interfaces, including
[`tendsto_pow_div_pow_atTop_zero`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Asymptotics/SpecificAsymptotics.html)
and continuity-based limit composition; the official
[review guide](https://leanprover-community.github.io/contribute/pr-review.html)
asks reviewers to check both an existing general result and the appropriate
file location. At the pinned Mathlib revision
`380f2aafb622cb2c1c93dac545b6389083c68c51`, the trigonometric API supplies
cosine identities and derivative limits, but no result for
$(\cos(\pi/L_n))^{t_n}$ under the diffusive hypotheses. The local theorem
`Real.tendsto_cos_pi_div_rpow_zero` therefore states that analytic consequence
in `Analysis/SpecialFunctions/Trigonometric/LogAsymptotics.lean`, using the
previously established limit $L^2\log\cos(\pi/L)\to-\pi^2/2$.

The former `Mogulskii/Spectral/Scaling/Power.lean` only specialized that
analytic theorem to the finite-interval width $N_n+1$ and proved the geometric
logarithmic correction used by two clients. Those wrappers have no callers
outside the same upper-rate proof chain. The correction is obtained directly
from the generic cosine-power limit, continuity of `log` at $4$, and
$L_n^2/t_n\to0$; it does not require a separate public theorem. The redundant
Mogulskii wrappers were removed, and the two clients now use the analytic
theorem and ordinary limit rules in their proofs. This leaves the public
analysis result independent of random walks while keeping the concrete
geometric estimate within its proof chain.

## Brownian first-window abstraction review (2026-10-23)

The candidate path abstraction is already present as
`ProbabilityTheory.firstNonnegativeWindowStartUpTo_eq_coe_iff_runningMinimum`
in `Probability/Process/Path/AboveStart/FirstWindow/Time/RunningMinimum.lean`. For a continuous
path $f$, it characterizes $T^s(f)=t$ by $t+1\le s$, constancy of the running
minimum on $[t,t+1]$, and minimality of $t$ among admissible starts. The
statement needs no Brownian law or probability measure, and is therefore the
appropriate reusable interface. A new sliding-window-minimum process would
only duplicate this equivalence.

With $m_f(v)=\min_{0\le r\le v}f(r)$, its exact relation is
\[
T^s(f)=t\iff t+1\le s\ \land\ m_f(t+1)=m_f(t)\ \land\
\forall u,\ (u+1\le s\land m_f(u+1)=m_f(u))\Rightarrow t\le u.
\]

`RunningMinimum.lean` owns this core path characterization and the record
identity. The path-level first-window modules group time-functional results in
`AboveStart/FirstWindow/Time/`, path transforms in
`AboveStart/FirstWindow/Shift/`, and complete pathwise endpoint-return
consequences in `AboveStart/FirstWindow/EndpointReturn/Basic.lean`; these
remain independent of any Brownian law. The rational-time covering steps used
by Bolthausen's Brownian nullity argument are proof support in
`AboveStart/FirstWindow/EndpointReturn/Lemmas/RationalCover.lean`. The
within-window return equivalence and endpoint-return case split are private to
their defining module because their only clients are in that same proof.

The online comparison used the official Mathlib documentation for
[`MeasureTheory.hittingBtwn`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/HittingTime.html)
and the Brownian invariances in
[`Mathlib.Probability.BrownianMotion.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/BrownianMotion/Basic.html),
then checked the corresponding pinned sources: Mathlib
`380f2aafb622cb2c1c93dac545b6389083c68c51` and BrownianMotion
`d6d901b6df592a543b7edf221f92d2ee6760d18d`. `hittingBtwn` expresses first
entry of a process into a state set, while the first-window predicate
quantifies over a full unit of future path values; the former is not a direct
replacement. Standard Brownian shift and scaling laws are already provided by
Mathlib: in particular, for fixed $t_0$, the shifted process
$u\mapsto B(t_0+u)-B(t_0)$ is Brownian. No additional public
stochastic-process wrapper is warranted.

The placement now separates the reusable Brownian fact
`IsBrownianReal.ae_aboveRunningMinimum_pos`, moved to
`Brownian/Reflection/Path/AboveRunningMinimum.lean`, from first-window-only
proof support. The estimates for non-antitonicity, existence of a positive
window, the $s-1$ cutoff atom, and interior/endpoint returns are under
`Brownian/AboveStart/FirstWindow/Lemmas/`; `Basic`, `Continuity`, and the
shift modules use ordinary imports for those helpers. The pathwise theorem
`IsBrownianReal.ae_endpointReturn_hittingTimeRightLimit` remains outside that
folder as a complete relation between first-window endpoint returns and the
descending hitting-time process. These results formalize Bolthausen, Lemmas
2.2--2.5, and Theorem 3.2, DOI 10.1214/aop/1176996098.

The helper estimates for non-antitonicity and finite-horizon interior and
endpoint returns have no clients outside their defining files, so their
declarations are `private`; the unrestricted existence and return results
remain module-visible for the first-window entry modules that use them.

## Gaussian escape-scale witness review (2026-10-23; updated 2026-10-29)

The reusable scale fact is `Asymptotics.isSmallDeviationScale_natCast_rpow_of_lt`, which covers every pair $0<p<q$. `IsMogulskiiScale` is the $q=1/2$ specialization. The particular sequence $n^{1/4}$ is now needed only in the Gaussian escape-coefficient proof; that proof applies the general power theorem locally. The one-client `Scale/Canonical.lean` wrapper has been removed, and no second scale predicate is introduced.

## Power-law small-deviation abstraction review (2026-10-23)

`Stable/SmallDeviation/EscapeRate/PathLaw/Basic.lean` previously defined the
scalar condition
\[
C<0,\qquad p(\varepsilon)>0\text{ eventually},\qquad
\varepsilon^\alpha\log p(\varepsilon)\longrightarrow C
\quad(\varepsilon\downarrow0),
\]
inside the stable-process path-law module. The condition itself uses no stable
law, path, or tube event. It is now owned by
`Probability/MeasureTheory/Asymptotics/SmallDeviation.lean` as
`HasPowerLawSmallDeviationRate`; the stable module uses this predicate
directly inside `HasStableProcessEscapeRate`, which remains the process-law
package. The positive-exponent assumption follows from the strictly stable
index in the specialized use. The radius-scaling identity is proved once at
the scalar level.

The literature uses the small-deviation/small-ball quantity
$-\log\mathbb P[\|X\|\leq\varepsilon]$ as the basic rate object. Aurzada's
article explicitly formulates this quantity for a random variable in a
normed space and studies its behavior as $\varepsilon\to0$; see
F. Aurzada, “Path regularity of Gaussian processes via small deviations,”
*Probability and Mathematical Statistics* 31(1) (2011), 61--78, equation (1)
and Section 2 ([published article](https://www.math.uni.wroc.pl/~pms/files/31.1/Article/31.1.4.pdf),
[arXiv:0905.3358](https://arxiv.org/abs/0905.3358)). Mathlib's official
[review guide](https://leanprover-community.github.io/contribute/pr-review.html#location-location)
asks whether a more general result already exists and whether the proposed
interface is general enough for future use. The online API check and a search
of the pinned Mathlib source at revision
`380f2aafb622cb2c1c93dac545b6389083c68c51` found general filter-limit,
real-power, and regular-variation machinery, but no predicate for this
power-law logarithmic small-deviation rate. The repository's discrete
`LogarithmicRate.lean` handles ENNReal-valued sequences at infinity; it does
not express a real-valued radius function at zero. Thus the new declaration
adds the missing scalar asymptotic interface without introducing a second
measure or process abstraction.

## Positive representatives of divergent scales (reviewed 2026-10-29)

The earlier public declaration `Asymptotics.exists_eventuallyEq_pos_of_tendsto_atTop`
was used only by the finite Gaussian partition proof. It has been removed from
the public scale API and its short `max 1 scale` construction now sits inside
`Mogulskii/Rate/Partition/Finite.lean`, where its sole use is clear. The
generalized slow-diagonal estimate was also moved from `Scale/SlowDiagonal` to
`Sequence/SlowDiagonal`, its semantic owner. This follows the repository's
reuse rule: a one-use helper stays local, while a complete sequence-limit
interface remains in the general sequence-asymptotics layer.

## Conditional positive definiteness and the Lévy integrand (2026-10-23)

The conditionally positive definite (CPD) quadratic-form interface and its
general closure operations belong to
`Analysis/Fourier/ConditionallyPositiveDefinite/Basic.lean`. The reusable
drift kernel is stated there for every additive group `G` and additive map
`φ : G →+ ℝ`: `x ↦ a φ(x) I` is CPD. The real Gaussian kernel
`x ↦ -x²` is grouped there as another basic CPD example. These results are
mathematical facts about CPD kernels, rather than steps in the Lévy–Khintchine
construction, so a separate one-lemma module would not clarify their owner.

The fixed-`x` compensated kernel and its Lévy-integral properties stay with the
integrand in `Probability/Distributions/InfinitelyDivisible/LevyKhintchine/Integrand.lean`.
The triple's exponent, continuity, CPD, and Hermitian properties are grouped
with the triple in `Defs.lean`. The general convolution-semigroup API and the
CPD-log result belong in `Semigroup/Basic.lean`; the semigroup's Lévy–Khintchine
decomposition is the complete result in `Semigroup/LevyKhintchine.lean`.
`Representation.lean` is the entry for the three infinitely-divisible-law
representation theorems. Its characteristic-function extraction and
measure-extraction proof chain is grouped under `Lemmas/Representation/`.

The review compared the declarations with the pinned Mathlib source at revision
`380f2aafb622cb2c1c93dac545b6389083c68c51`: its Fourier source does not define
either the repository's `IsPositiveDefinite` function predicate or an
`IsConditionallyPositiveDefinite` quadratic-form API. The latter therefore
extends the repository's existing positive-definite interface. Mathlib's
official review guide asks reviewers to check the
declaration's home, existing general statements, import boundaries, and whether
a new file improves imports or separates an overly long or mixed-topic module
([location guidance](https://leanprover-community.github.io/contribute/pr-review.html#location-location)).
The CPD examples therefore extend the existing CPD interface, while the
Lévy-specific integral facts remain beside their defining integrand.

The first-order exponential limit and the imaginary-axis cubic remainder estimate
are used only inside this representation proof chain. The former follows from
Mathlib's `HasDerivAt.tendsto_slope_zero`; the latter specializes
`Complex.exp_bound` at order three. They are grouped in
`Probability/Distributions/InfinitelyDivisible/LevyKhintchine/Lemmas/Representation/Exponential.lean`,
so they have one proof-support module rather than separate files or a public
analysis API duplicating those general tools. This follows the repository's
`Lemmas/` rule and Mathlib's location review guidance; the matching pinned
sources are `Vendor/Mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean` and
`Vendor/Mathlib/Mathlib/Analysis/Complex/Exponential.lean`.

## Characteristic-function and Lévy truncation ownership review (2026-10-23)

`Probability/Distributions/CharacteristicFunction/Zero.lean` contains the
complete midpoint estimate: if a probability measure on a real inner product
space has `charFun μ ξ₀ = 0`, then
`‖charFun μ ((1 / 2) • ξ₀)‖ ≤ 3 / 4`. This is an independent result about
characteristic-function zeros, so it has a public semantic owner even though
the current client is the nonvanishing proof for infinitely divisible laws.
The client-specific step that repeatedly halves a zero remains private in
`Probability/Distributions/InfinitelyDivisible/CharacteristicFunction/Basic.lean`;
the nonvanishing theorem, continuous-logarithm existence, and Hermitian-log
property are grouped there as the characteristic-function API of infinitely
divisible laws. The midpoint theorem is stated for every real inner product
space because the pinned characteristic-function positive-definiteness
result supports that domain. No radius- or infinitely-divisible-specific
alias is retained.

The pinned Mathlib source at revision
`380f2aafb622cb2c1c93dac545b6389083c68c51` defines characteristic functions in
`Vendor/Mathlib/Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.lean`;
it has no corresponding midpoint estimate. The project positive-definiteness
extension applies to real inner product spaces in
`MeasureTheory/Measure/CharacteristicFunction/PositiveDefinite.lean`, and the
new estimate uses that interface. Mathlib's official review guide says to
check whether a new file improves import boundaries or separates an overly
long or mixed-topic file, and to compare a proposed result against more
general existing statements ([location guidance](https://leanprover-community.github.io/contribute/pr-review.html#location-location)).

The unit small-jump region `{x | |x| < 1}`, the radius-`ε` large-jump region
`{x | ε ≤ |x|}`, their measurability and membership facts, and the
large-jump antitonicity now belong to the proof-support module
`Probability/Distributions/InfinitelyDivisible/LevyKhintchine/Lemmas/JumpRegions.lean`.
The formula `levyCompensatedIntegrand ξ x = exp(i x ξ) - 1` for `1 ≤ |x|`
belongs to `LevyKhintchine/Integrand.lean`, since it is a complete property
of the integrand and does not depend on a convolution semigroup. The obsolete
`smallSet`/`largeSet` names were replaced by `smallJumpSet`/`largeJumpSet`
without compatibility aliases. These set names occur only in proof bodies, and
internal clients load them with `import all`. The characteristic-function extraction and
Lévy-triple assembly are proof stages under
`LevyKhintchine/Lemmas/Representation/`; the finite canonical-measure limit
theorem is exposed in `Semigroup/CanonicalMeasure/Existence.lean`. Its integral
identity and mass/tail estimates are grouped in
`Semigroup/CanonicalMeasure/Lemmas/Bounds.lean`. The tilted scaled measure
itself is defined in `Semigroup/CanonicalMeasure/Basic.lean`, and the resulting
Lévy-measure construction is exposed in `Semigroup/LevyMeasure.lean`. The
scaled small-jump drift limit and characteristic-function decomposition are in
`Drift.lean`. The public semigroup decomposition is in
`Semigroup/LevyKhintchine.lean`, while `Representation.lean` exposes the three
probability-law representation theorems. The generic
first-order complex exponential limit belongs to
`Analysis/SpecialFunctions/Complex/Exponential.lean`; the one-use cubic
remainder specialization stays private in `SmallJumpIdentification.lean`.

The canonical displacement `h(x)=x 1_{|x|<1}` and its first-moment
integrability result are shared by the stable jump model, Poisson characteristic
functions, and finite-variation Lévy theory. They now live with the Lévy cutoff
interfaces in `MeasureTheory/Measure/Levy/Cutoff.lean`; the generic small-jump
mean and uncompensated-drift definitions, complex compensation identities, and
uncompensated-integrand identities live in
`LevyKhintchine/FiniteVariation.lean`. The generic unit-time product
integrability consequence for restricted small-jump marks lives in
`Probability/RandomMeasure/Poisson/Intensity/LevyCutoff.lean`; stable moment and
drift consequences remain under `Probability/Distributions/Stable/LevyMeasure/Cutoff/`. The literature gives a more general
truncation function `h` that is bounded and equals `x` near zero, with the
canonical `x 1_D` as a standard example (Baurdoux--Papapantoleon, *An
Introduction to Lévy Processes*, §5, Definition 5.6 and Example 5.9(i)). The
existing Lévy triple and exponent use the unit canonical cutoff throughout;
parameterizing that whole API by arbitrary `h` would change its drift
convention, and current clients use only the canonical choice. We therefore
move the reusable canonical map to the Lévy-measure cutoff layer without
introducing a broader truncation-function abstraction.

The measure-generic null-fiber selection theorem is in
`MeasureTheory/Measure/LevelSet.lean`: for an s-finite measure, measurable
`g : α → β`, and an uncountable set `S ⊆ β`, some `r ∈ S` satisfies
`μ {x | g x = r} = 0`. The codomain only needs measurable singletons. It turns
Mathlib's countability theorem for positive-measure level sets into a selector
for arbitrary uncountable subsets. The Lévy-specific selector for radii with
null spheres `{x | |x| = r}` is currently used only by the Lévy–Khintchine
representation proof chain. The chain keeps that adapter under
`LevyKhintchine/Lemmas/Representation/Lemmas/AtomFreeRadii.lean`; the generic
null-fiber theorem remains at `MeasureTheory/Measure/LevelSet.lean`, while
finite mass away from zero remains beside `IsLevyMeasure` in
`MeasureTheory/Measure/Levy/Basic.lean`. This places the reusable abstractions
at their general owners and the application-specific radius selection with
the proof chain that needs it.

Brownian range small-width estimates belong to
`Probability/Process/Brownian/SmallDeviation/Range/`: the fixed-corridor
spectral bound and the logarithmic rate are complete Brownian probability
interfaces. The short Rademacher Donsker transfer used only inside the spectral proof is
a `private` lemma in `FiniteCover.lean`. The finite-time Rademacher path range
and rounded interval survival statements remain under
`RandomWalk/Rademacher/FiniteInterval/Range/`; the arbitrary centered
unit-variance block Donsker comparison remains under
`RandomWalk/SmallDeviation/Range/`.

## Reserve-spine restart endpoint law review (2026-10-23)

The initial 2026-10-23 review placed the root-indexed finite-rank selector at
a stopping generation in
Probability/BranchingRandomWalk/Selection/NSelection/AtStoppingTime.lean.
It defines the selector by

    p_i(ω) = particleAtRankBy(v_n(ω), A_n(ω), i) if τ(ω) = n,
    p_i(ω) = none                         if τ(ω) = ∞,

and provides measurability and rank-vector properties for adapted finite-stage
data. Mathlib's Probability.Process.Stopping supplies general stopping-time
and stopped-process APIs, but not an order-statistic selector whose candidate
set varies with the generation. The new declaration is therefore the generic
N-selection adapter, not a restart-specific helper. This comparison was made
against the pinned Mathlib source at revision
380f2aafb622cb2c1c93dac545b6389083c68c51 and the
[official stopping-process module documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/Stopping.html).
This initial placement was corrected on 2026-10-30 after auditing the full
signatures: the definitions quantify over arbitrary candidate types and carry
no branching data. A follow-up semantic review separated generic ranked-selector
measurability from evaluation at a stopped process. The former stays under
`MeasureTheory/Selection/NSelection`; the latter now lives at
`Probability/Process/Stopping/Selection/Ranked.lean`, because its construction
and measurable rank-vector laws use the stopping-time and stopped-σ-algebra
interface owned by Mathlib `Probability/Process/Stopping`. Declarations remain
in the generic selector namespace `Combinatorics.Selection.NSelection`.

The measurable rebasing map for a random countable-range family of rooted
subtrees belongs to
Probability/BranchingRandomWalk/Genealogy/Exploration/RootIndexed/SelectedSubtrees/FixedFamily.lean.
Its statement allows arbitrary root, family-index, and child-slot types under
the assumptions needed for countable measurable fibers. This is a reusable
RootIndexed field operation. Mathlib's generic countable measurability
principles, including measurable_to_countable, do not encode the address
concatenation and root-indexed field reindexing in this statement; the project
theorem specializes those principles to that general field construction. See
the [official measurable-space constructions documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Constructions.html).

The restart-specific declarations remain with their semantics:
Restart/RootedTrial/Reserve/Causal.lean defines candidates observable from
the reserve spine and their source population, including the inclusion of the
live spine address in the source slice;
Restart/RootedTrial/Coupling/ReserveSpine.lean compares that source with the
rank-installed first-N population;
Restart/RootedTrial/Reward/PositivePart.lean owns the pathwise edge-sum and
source-minimum positive-part estimates; the deterministic one-step cutoff
inequality belongs to `Combinatorics/BranchingWalk/Step/Selection/ReserveSpine`.
`Reward/Expectation.lean` integrates the pathwise estimate using the
fixed-generation sampled-step law. Its first-slot positive-potential
observable is shared with the deterministic branching-step selection layer,
and its measurability result is owned by the corresponding MeasureTheory
adapter;
Restart/RootedTrial/Completion/Endpoint.lean defines the first-success
completion time and its rank-installed endpoint vector;
EndpointFreshField.lean states the joint product law of endpoint positions
and their fresh descendant field;
FixedHorizon.lean pushes that law through a fixed-horizon population
observable; and EndpointHorizon.lean gives the time-position-field law and
its measurable-observable consequence. The root-family, address-geometry,
and fresh-field factorization stages used only in that proof chain are under
Completion/Lemmas/EndpointHorizon/. The product law is a complete reusable
probability statement, so it remains outside Lemmas/; the short pushforward
steps and factorization intermediates remain in the proof subtree.

The split replaces the mixed Coupling/Basic.lean module; no forwarding
aliases preserve its old path. The endpoint modules are not all independent
theorem entries: Endpoint.lean defines stopping data, while the joint law,
fixed-horizon law, and endpoint-horizon law are the public probabilistic
interfaces.

`Completion/RootIndexed/CapStopped.lean` also exposes
`RootIndexed.capStoppedPopulationAt_selectedRoot_measurable`: a root whose
fibers are measurable at generation $s$ and whose address has depth $s$ gives
a rooted cap-stopped population measurable at generation $s+a$. The theorem
is stated for an arbitrary measurable selected root, so it is part of the
root-indexed cap-stopped interface; the reserve-lineage specialization is
proved at its caller. `Completion/Lemmas/` contains only its remaining
theorem-specific proof steps.

Within `Restart/RootedTrial/Spine/`, `ReservePath.lean` owns the recursive
second-child reserve path, its lineage and causal-population interfaces. The
deterministic rule that chooses the second selected child at a split, the
first for a singleton, and `⊥` for an empty selection is owned by
`Combinatorics/BranchingWalk/Step/Selection/ReserveSpine.lean`;
`Splits.lean` owns the live split count, its stopping time, and the identities
between an absolute reserve path and its recursively rooted subtree;
`SelectedRoot.lean` lifts split-completion stopping times to selected roots;
`SiblingTrial.lean` gives the complete factorization of first-child growth and
second-child reserve events; and `BoundedOffspring.lean` turns the reserve rule
into a finite-slot Galton--Watson law and a uniform growth estimate. These
statements expose the construction's objects and probability interfaces to
the neighboring `Reserve/` and `Coupling/` modules. Their local calculations
prove those named interfaces rather than forming a separate reusable
proof-only chain, so this group does not need another `Lemmas/` subtree.

## Finite-slot population coupling

`Probability/BranchingRandomWalk/Restart/RootedTrial/FiniteSlot/Coupling.lean`
owns the coded active-label set, the generation's offspring row and its product
law, and the pathwise and conditional first-moment recursions. Its principal
objects are

    Aₙ(ω) = {u : Fin n → Fin 2 | u survives in the coded tree},
    |Aₙ₊₁(ω)| = ∑_{u ∈ Aₙ(ω)} childCount(Lₙ(ω)(u)),
    Aₙ ⫫ Lₙ.

The finite address, encode/decode, and level-root arguments that identify the
binary labels with the selected source population are proof support specific
to this coupling. They are grouped in
`Probability/BranchingRandomWalk/Restart/RootedTrial/FiniteSlot/Lemmas/Coding.lean`.
The general selected-path predicate and its equivalence with membership in a
finite step-selected generation belong to
`Population/Processes/StepSelection/SelectedPath.lean`; they do not depend on
the binary finite-slot encoding and are available as part of the selection
process API.
The source module still uses legacy import syntax because its existing
mathematical dependencies have not been migrated to Lean's `module` syntax;
its direct helper import therefore uses plain `import` rather than `import all`.
`Moments.lean` consumes the generation-law and recursion interface, and
`Growth.lean` derives the bounded-population probability estimate from those
moments.

The nonemptiness implication
`StepSelection.population_nonempty_of_all_selected_marks_nonempty` is owned by
`Population/Processes/StepSelection/Basic.lean`: it requires only a nonempty
selected family at every visited mark and applies to every finite-step
selection. The conversion from this fact and the binary population bound to a
complete trial event belongs to `Restart/Trial/Basic.lean`, beside the
definition of `growthTrialSuccess`. Neither implication needs an individual
module.

`Moments.lean` also identifies the real mean of the encoded binary-slot law
with the real value of `OffspringConfigurationLaw.expectedChildCount`.
`Growth.lean` uses that conversion and
`finiteOffspringLaw_isSupercritical` from `FiniteSlot/Offspring.lean`, so the
nonempty-and-split criterion is proved once in the offspring-law layer.

The integrated population moment formulas
`finiteSlotPopulationSizeReal_integral_eq_pow` and
`finiteSlotPopulationSizeReal_sq_integral_eq_recursion` now sit in
`FiniteSlot/Moments.lean` beside their one-step recursions. `FiniteSlot/Growth`
contains the finite-slot probability estimates and no longer depends on the
reserve-candidate layer. The two results that combine these estimates with a
reserve cutoff or an observable reserve candidate are grouped in
`Reserve/GrowthSuccess.lean`, above both contributing modules in the import
graph. This groups a coherent public result family without creating one file
per helper lemma.

The generic selected-slot, split, and `growthTrialSuccess` definitions remain
in `Restart/Trial/Basic.lean`. The separate root-indexed candidate family—first
child addresses, completion times, event measurability, and the first-failure
integral estimate—lives in `Restart/Trial/RootIndexed.lean`. Those declarations
form a complete root-indexed construction and are public interfaces, so the
file is a semantic module rather than proof-only support under `Lemmas/`.

## Generic N-selection mechanisms and branching-walk layers

`Combinatorics/Selection/Basic.lean` owns selection mechanisms on arbitrary
candidate sets. `Combinatorics/Selection/NSelection/Basic.lean` adds capacity
and the finite first/last-$N$ rules. `Mechanism/` owns ordered finite and
lower-finite selectors, dynamic-value tie-breaking, rank lookup, threshold
comparison, and order-dual transport. `Matching/` owns the generic Hall and
equal-rank lower-tail matching interfaces. These modules use no branching-walk
objects and are reused by probability and deterministic clients.

Mathlib's `Finset.sort`, `Finset.orderIsoOfFin`, and `Finset.orderEmbOfCardLe`
provide finite order enumeration and embeddings. Mathlib's Hall API provides
matching for an arbitrary relation. The moved modules add capacity selectors
on arbitrary sets, value-key first-$N$ specifications for lower-finite
populations, and the lower-tail forms used by the project.

`Combinatorics/BranchingWalk/Selection/Coupling/` contains the branching-walk
cloud, offspring, one-step, and pathwise domination results. Its
`NSelection/Walk/` subtree defines the deterministic selected walk, clouds,
frontiers, and frontier speeds. Random laws and measurable selection processes
remain in the probability layer. No compatibility aliases retain the old
BranchingWalk module paths or namespaces.

## Initial-population speed transport

The generic finite order-statistic comparison by lower-tail counts belongs to
`Combinatorics/Selection/NSelection/Mechanism/Finite/AtRank.lean`.
The value-preserving candidate-bijection theorem belongs to
`Matching/ByRank.lean`, and lower-tail Hall matching belongs to
`Matching/Hall.lean`.

The ranked offspring-batch law is part of
`AsymptoticSpeed/Selection/PopulationBatch.lean`, beside the ranked-root
construction and its independence theorem. These declarations used to share
`InitialPopulation/Speed/Basic.lean` with unrelated branch-random-walk glue;
that mixed module has been removed.

Within `InitialPopulation/Field/`, `Fresh.lean` owns the capacity-hitting
time, its canonical root enumeration, and the stopped selected-subtree field
law. `Independence.lean` gives the joint product formula for the hit-position
vector and fresh field. The jointly measurable population and endpoint maps
are in `Population/Processes/Selected/ParameterizedRootIndexed.lean`: they
depend only on the root-indexed selected-process recursion and a variable
initial position vector, so the population-process layer owns them
independently of the asymptotic-speed argument.

`InitialPopulation/Speed/Transport.lean` owns the measurable endpoint and its
almost-sure asymptotic-speed transport under the product of the initial
population law and the root-field law. The former
`InitialPopulation/Limit/ProductAlmostSure.lean` only wrapped Mathlib's
measurable-set product-measure theorem for this one event and had one caller.
It was inlined at the semantic owner and removed; the Mathlib interface remains
the general reusable result.


## Endpoint-band and endpoint-window ownership (2026-10-26)

The strict endpoint-band event and corridor-bridge interfaces have no
Mogul'skii scale or moment assumptions, so their owner is
`HorizontalTube/EndpointBand/`. Its `Basic.lean` defines measurable finite-path
events; `Iteration.lean` proves the killed-kernel and repeated-block
consequences; `Donsker/Normalized.lean` supplies the centered unit-variance
functional-limit transfer. The endpoint-window subtree also retains the closed tube event with a terminal
fraction interval in `EndpointWindow/Basic.lean`, used by the finite-variance
results. The strict open-tube API with independently varying mesh spacing and
window half-width lives in `EndpointWindow/Iteration.lean`, followed by its
finite-return iteration and varying-horizon Donsker transfer. Mogul'skii's
seven-window spectral construction remains in `Mogulskii/Lemmas/EndpointBands/`
because that placement and its spectral estimates are source-specific. The
move follows statement hypotheses and semantic ownership; cross-module use was
not the promotion criterion.

## IID finite-prefix bridge comparison

`Probability/Sequence/IID/Blocks/FiniteCover.lean` owns the finite-cover
inequality for an IID sequence on an arbitrary measurable space. Its
assumptions are measurable prefix and following-block events, their IID
factorization, and a finite cover; it does not use addition, path geometry,
moments, or scaling. The adjacent
`Probability/Process/RandomWalk/Path/Block/Corridor/FiniteBridge.lean` module
retains the path-limit bridge-mass and logarithmic comparison results, which
consume application-specific normalized path events. The generic inequality
therefore belongs with IID block factorization, while the bridge application
remains with random-walk corridor paths.

## Sequence prefix filtration and independence

`Probability/Sequence/Filtration.lean` defines the strict prefix filtration
`𝓕_n = σ(X_0, …, X_{n-1})` for arbitrary measurable coordinate types. The
matching Mathlib candidates were checked at pinned revision
`380f2aafb622cb2c1c93dac545b6389083c68c51`, in
`Vendor/Mathlib/Mathlib/Probability/Process/Filtration.lean`: `Filtration.piLE`
uses coordinates `≤ i`, while `Filtration.natural` requires topological,
metrizable Borel coordinate types and strongly measurable process maps.
Neither has the strict `< n` indexing with only a measurable-space assumption,
so the local definition remains. The file now imports Mathlib's base
`Probability.Process.Filtration` directly rather than the higher-level
`Adapted` module. See [the official Filtration API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/Filtration.html)
and the [pinned Mathlib source](https://github.com/maix00/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/Probability/Process/Filtration.lean).

The theorem that an independent coordinate is independent of all earlier
coordinates accepts an arbitrary measurable domain and an arbitrary
`iIndepFun` family; it does not assume an IID sequence law. Its module was
therefore moved from `Probability/Sequence/IID/Filtration.lean` to
`Probability/Sequence/IndependentPrefix.lean`. The theorem is the finite
prefix specialization of Mathlib's general `indep_iSup_of_disjoint`, with
index sets `{k}` and `Set.Iio n`; the local statement presents the same result
using the common `Fin n` prefix interface. This comparison is documented in
[the official independence API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html#ProbabilityTheory.indep_iSup_of_disjoint)
and the [pinned Mathlib source](https://github.com/maix00/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/Probability/Independence/Basic.lean).
The random-walk adaptedness module now imports the strict-prefix filtration
directly and does not pull in this independence interface transitively.

The sequence block and prefix-filtration modules now have exact public
declaration inventories in their headers. The affected filtration,
random-walk adaptedness, stopping-time, and drifted-tube modules build with
the pinned toolchain; the renamed independent-prefix axiom test compiles, the
import-boundary checker passes its 10 public entries, and the run-all-test
manifest points at the renamed test. The complete file, namespace, and
citation audit remains open.


## Mogul'skii rate-bound ownership

`Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Rate/Bounds/` has four theorem entry modules: `Lower.lean` transfers a uniform killed-walk return-block bound to a logarithmic lower rate; `StrictInterior.lean` constructs such a bound for a horizontal tube containing the origin in its interior; `Upper.lean` gives coarse diffusive-block bounds; and `SharpUpper.lean` gives the sharp horizontal-tube upper rate. The five nested proof modules (including the nested `Lemmas/SharpUpper/`) are one-use derivations and remain internal to this proof family.

The endpoint-CLT bridge stays in `Lemmas/EndpointCLT.lean`: Mathlib's central limit theorem and Portmanteau results provide the abstract convergence tools, while the local composition includes the diffusive block schedule, killed-walk kernel, and a uniform-in-starting-point survival bound used only here. The finite-cover block step specializes the arbitrary-block estimate owned by `RandomWalk/SmallDeviation/Range/FiniteCoverUpper`; its Mogulskii specialization does not warrant a second public copy.


## Gaussian stable-process escape constant

`Probability/Process/Stable/SmallDeviation/EscapeRate/Gaussian.lean` owns the exponent-two Gaussian stable-process escape-constant theorem. The statement concerns the stable-process escape-rate interface and is consumed by both Brownian path-law and normal-domain Mogul'skii results. Its proof uses the Rademacher path-class calibration in `RandomWalk/SmallDeviation/Mogulskii/Gaussian/Lemmas/NormalConstant.lean`; that proof-specific calibration remains with its mathematical construction, while the resulting reusable escape-rate theorem lives beside `HasStableProcessEscapeRate`. All former imports of the Mogulskii-local `Gaussian/EscapeConstant` path now use the stable escape-rate owner.


## Mogul'skii Gaussian rate support

The finite Gaussian block lower-bound construction stays in `RandomWalk/SmallDeviation/Mogulskii/Gaussian/Blocks/Lemmas/`: it is used only by the finite-partition rate proof. Its reusable foundations are already owned by `FunctionalLimit/FiniteDimensional/IndependentBlocks` (joint limits of consecutive blocks), the convergence-in-distribution Portmanteau API (open-set probability bounds), and `Kernel/Killed/Return/Comparison` (finite-reference return-kernel transfer). The Gaussian modules provide the theorem-specific diffusive specialization. `Gaussian/Lemmas/NormalConstant` is the one-use Rademacher calibration for the public escape constant.

The explicit path-class rate, source-terminal-left probability rate, and source-terminal-left inner/outer theorem remain separate public interfaces because their path conventions and conclusions differ. The public Gaussian stable-process escape constant is owned by `Process/Stable/SmallDeviation/EscapeRate/Gaussian`, where `HasStableProcessEscapeRate` is defined; its proof-specific Rademacher calibration remains in the Mogulskii Gaussian lemma directory.


## Stable-scale multiplier construction

`Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Scale/SlowMultiplier.lean` exposes the stable-time specialization of the generic regular-variation diagonal construction. The generic multiplier selection remains in `Analysis/Asymptotics/RegularVariation/SlowScale`; this module adds the stable-scale outputs and the version preserving arbitrary fixed-parameter eventual conditions. These are complete constructions for the stable-scale API, so they live beside `IsStableMogulskiiScale`, outside proof-only `Lemmas/`.


## Stable Mogul'skii scale and rate interfaces

`Stable/Scale/Basic` composes `IsStableNorming` with the generic `Analysis/Asymptotics/Scale/Basic.IsSmallDeviationScale`. `Stable/Scale/BlockLength` and `BlockCount` specialize the generic floor-block limits under `Analysis/Asymptotics/Scale/Block/` using the law-dependent stable time; the index-two module connects this scale to the existing diffusive block length. Stable rate vanishing stays with the stable norming and its slowly varying truncated-moment factor.

`Stable/Corridor` owns stable one-block tube events and their path-limit transfers. `Stable/Rate/Upper` delegates generic power-to-logarithmic-rate and quotient-count facts to `Probability/MeasureTheory/Asymptotics/LogarithmicRate` and `Analysis/Asymptotics/Scale/Block/Count`. `Stable/Rate/Lower` and `Upper` hold the complete source-facing rate bounds and limit interfaces; proof-only derivations remain under nested `Lemmas/`.

`Stable/Discrete/FromIncrementLaw/Normal/HorizontalTube/Basic` owns the finite-variance closed-tube rate from Wang Yiyang, Chapter 3, Lemma 3.1(i), with its Mogul'skii Theorem 3 input. `Scales` gives complete sampled-width, real-width, and generalized-inverse formulations; the generic scale predicates, inverse scales, and sampled-time limit transfer stay in `Analysis/Asymptotics/Scale`, while the random-walk probability rate remains with its law-specific owner. `EndpointWindow` is the corresponding complete terminal-window rate for Chapter 3, Lemma 3.1(ii). Its corridor-union construction is a one-use transfer, so it stays under the single nested `Normal/HorizontalTube/Lemmas/` directory. These source-facing theorem interfaces are distinct from the stable-process path-rate theorems and remain outside `Lemmas/`.

`Stable/Discrete/FromIncrementLaw/Normal/PositiveNormalization` and `Stable/Normalization` convert raw domain-of-attraction inputs into the Gaussian and stable Mogul'skii normalizations used by the source-facing rates. The stable rescaling and time reindexing depend on both the increment law and the Mogul'skii scale, so they stay under `FromIncrementLaw`; generic scale and stable-law operations remain in their respective analysis and probability modules. `FromIncrementLaw/Path/Realization` owns the complete arbitrary-i.i.d.-coordinate path-class rate record and its ordinary-probability consequence. `Path/ContinuousBoundary` and `Path/RealizationContinuousBoundary` provide complete continuous-boundary specializations for canonical and arbitrary i.i.d. realizations. The shared finite-corridor approximation and law-transfer tools are already owned by the path-class and sequence-law modules; no additional reusable abstraction is needed here.


## Mogul'skii equation-(34) bridge proof support

`Stable/Discrete/Bridge/Events` owns the source base-corridor and terminal-endpoint events with the original `(c,b]` convention. The supporting endpoint geometry, finite-center cover, entrance-mass comparison, endpoint-corridor decay, and logarithmic ratio are one-use stages grouped under `Bridge/Lemmas/`. Their finite block decomposition reuses `Path/Block/Corridor/FiniteBridge`, and entrance positivity reuses the stable entrance modules. This keeps semantic events public at their owner while proof-specific equation-(34) steps remain internal.


## Stable discrete endpoint estimates

`Stable/Discrete/Endpoint/BandTransfer/Rate` owns the public stable path-law endpoint-window estimates. `BandTransfer/Lower/CellBridge` owns the discrete endpoint-core return lower bound consumed by entrance and path-class partition results. `Endpoint/StablePathLaw`, `Endpoint/Upper`, and `Endpoint/StrictStable` expose separate lower, upper, and strict-attraction interfaces. Their proof-specific parameter, Portmanteau-transfer, seven-band iteration, and return-block assembly steps remain under the nested `Lemmas/` folders.


## HorizontalTube endpoint-window product ownership (2026-10-30)

`RandomWalk/SmallDeviation/HorizontalTube/Blocks/EndpointWindowProduct.lean`
exposes the finite endpoint-window product estimate for arbitrary schedules,
windows, admissible sets, and one-block probability bounds. Its public
statement is a complete horizontal-tube interface; its current use by the
drifted-tube proof does not determine its abstraction level. Generic
conditional-block multiplication remains in
`Probability/Process/Filtration/ConditionalBlocks.lean`. The two
horizontal-tube conditional-expectation calculations are private proof support
in `Blocks/Lemmas/ConditionalProduct.lean`, alongside their one-use product
assembly. `Blocks/EventBridge.lean` retains public event and translation
semantics, without exporting those conditional calculations.


## Rademacher finite-interval spectral audit (2026-10-30)

`Analysis/Asymptotics/Scale/CenteredInterval.lean` owns the generic rounding
from a positive real scale to the centered integer radius and the limits for
the associated even lattice widths. `Rademacher/FiniteInterval/` retains the
explicit killed-walk and sine-spectrum statements. The generic finite-kernel
row-sum estimate in `LinearAlgebra/Matrix/FiniteKernel/Eigenfunction.lean`
is the reusable interface; interval-specific existential row-sum wrappers
were removed. Mathlib's symmetric spectral theorem supplies a general
orthonormal eigenbasis, while the explicit discrete sine eigenvalues and their
ordering remain specific to the interval kernel.

## Selection ownership by semantic layer

A selector over arbitrary candidate sets is a general capacity-selection
mechanism and belongs under Combinatorics/Selection; it carries no
branching-walk structure. Once the candidates are offspring, the selected set
is iterated by generation, or the result is a selected branching walk, the
object has BranchingWalk semantics and belongs under
Combinatorics/BranchingWalk/Selection. Measurability interfaces for the
generic selector belong under MeasureTheory/Selection, while stochastic
laws and estimates for branching populations belong under
Probability/BranchingRandomWalk/Selection.

The distinction is visible in the types. A generic mechanism is a map
`M : Set ι → Set ι` with `M S ⊆ S`; its capacity-`N` refinement selects a
finite subset of each candidate set and bounds its cardinality. It is used
by branching-walk clients and by the independent stopping-time rank selector
in `Probability/Process/Stopping/Selection/Ranked.lean`. The branching-walk
`NSelection`, by contrast, maps whole branching walks to branching walks with
at most `N` children at each node. The measurable layer contains measurable
random or ranked selectors, not the generic deterministic selector itself.
This is consistent with Mathlib's object-first organization: its concrete
finite-set choice operation, [`Finset.choose` in
`Mathlib/Data/Finset/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/Data/Finset/Basic.lean),
is kept with finite-set operations in the pinned Mathlib revision
`380f2aafb622cb2c1c93dac545b6389083c68c51`; Mathlib does not provide the
project's abstract ranked capacity-`N` interface.

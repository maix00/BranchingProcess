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
| Optional child configurations and deterministic branching walks | `Combinatorics/BranchingWalk` | `Step`, `surviveAlong`, `BranchingWalk` |
| Unmarked branching specializations and genealogy projections | `Combinatorics/Branching` | `Basic.lean` specializes branching walks to unit marks; `Map.lean` forgets spatial marks while preserving the genealogy; `Tree/Basic.lean` names the Ulam--Harris genealogy type in the branching namespace. These are complete model adapters, not proof-chain lemmas. The generic invariance `surviveAlong_map_iff` belongs beside the `surviveAlong` predicate in `BranchingWalk/Basic/Survival/SurviveAlong.lean`. Mathlib's [`Quiver.Arborescence`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Quiver/Arborescence.html) represents directed trees by unique paths in a quiver; it does not replace the project's ordered Ulam--Harris address-tree interface. |
| Genealogy relations and generation sizes of deterministic branching walks | `Combinatorics/BranchingWalk/Basic/Genealogy` | `Descendant.lean` defines reachability along surviving finite paths, `Ancestor.lean` gives the converse relation and its generation-distance slices, and `GenerationSize.lean` counts generation slices and proves pathwise recursion and extinction monotonicity. Fixed-length list finiteness uses Mathlib's [`List.finite_length_eq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Finite/List.html); the prior local proof was removed. |
| Structural parent of a root-indexed address | `Combinatorics/UlamHarris/Relation` | `RootIndexed.parent` removes the final label of an address and preserves its root. This operation has no branching-walk or survival assumptions. Mathlib's [`RootedTree`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/SuccPred/Tree.html) models one tree through an ancestor order, while [`Quiver.Arborescence`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Quiver/Arborescence.html) models unique paths from one root; neither directly owns the project's `Root × List α` address operation. |
| Random branching steps, fields, laws, and point-measure observations | `Probability/BranchingRandomWalk/Step` | `Presentation/` separates coordinate sampling from optional fields; `Law/` owns one-step and product-field pushforward laws; `Field/` owns realization, generation-local updates, and boundary-weight events; `PointMeasure/` owns slot-multiplicity observations, their laws, and point-process adapters; `Position/Measurability` owns generation-filtration measurability. The deterministic step and point-measure objects remain in `Combinatorics/BranchingWalk/Step/`. |
| Split declarations along adapted branching lineages | `Probability/BranchingRandomWalk/Timing/Splits` | `Declared.lean` owns the event that a selected lineage reads a split mark at generation `n` and declares it at generation `n+1`, together with the first-declaration stopping-time theorem. The generic first-hit and one-generation event shift remain in `Probability/Process/HittingTime/Declarations`; the tree-specific event no longer sits in the deterministic Ulam--Harris layer. |
| Offspring configuration laws and Galton--Watson generations | `Probability/BranchingProcess` | `Offspring/` owns the law of complete optional child-slot configurations, mark maps, point-measure pushforwards, and the independently sampled address field; `GaltonWatson/` owns the presampled process law, descendant-field distribution and independence, and generation-size recursion and measurability. `GaltonWatson/Moments/Definitions.lean` defines the finite-slot moment quantities; `FirstMoment.lean`, `SecondMoment.lean`, and `PaleyZygmund.lean` expose their complete recurrences and probability bounds. The one-use finite-population and independent-field calculations are grouped under `Moments/Lemmas/`. `GaltonWatson/BoundedGrowth.lean` specializes the moment recurrences to finite-slot offspring. The fully abstract second-moment recurrence and probability bounds are owned by `Probability/MeasureTheory/Moments/SecondMomentGrowth.lean`. These are unmarked branching-process interfaces; spatial marks and branching-random-walk selection belong under `Probability/BranchingRandomWalk/`. |
| Branching-cloud slice order and particle domination | `Combinatorics/BranchingWalk/Cloud` | `Order/Slice` defines threshold-count comparison for measures and rankwise order on cloud slices; `Order/Basic` lifts it across all times; `Order/DominatingMap` and `Order/SliceDominatingMap` carry the corresponding injective matching; `Order/DynamicSelection` and `Order/Selection` transfer it through first-`N` selection |
| Deterministic finite and lower-finite selection | `Combinatorics/BranchingWalk/Selection/NSelection/Mechanism` | `Leftmost`, `ByValue`, and `AtRank` define finite label- and value-ordered selection; `Hall` and `Matching` construct injective comparisons; `Infinite` handles lower-finite candidate sets; `OrderDual` derives the rightmost API from the leftmost rule |
| Additive paths and finite block sums | `Algebra/BigOperators` | `AdditivePath`, `AdditivePath/Block` |
| Finite weighted-sum comparison bounds | `Algebra/Order/BigOperators/WeightedSum` | Bounds a weighted sum against the total mass when the masses are nonnegative and the weights lie in a fixed interval; the undivided bound assumes an ordered commutative ring, and the quotient bounds assume an ordered field |
| Natural exponents from real logarithmic ceilings | `Analysis/SpecialFunctions/LogarithmicCeiling` | Packages Mathlib's `Real.logb`, real-power monotonicity, and natural ceiling into $x\le b^{\lceil\log_b x\rceil_+}$ for $x>0$ and $b>1$; this is the reusable real-analysis estimate used to select integer exponential horizons. |
| Algebra of normalized finite weighted sums | `Algebra/BigOperators/WeightedSum/Cancellation` | Gives the normalization, weighted-average, and weight-cancellation identities for finite sums over an arbitrary field, without a probability-law assumption |
| Countable ENNReal sums over ordered pairs | `Topology/Algebra/InfiniteSum/ENNReal` | `PairPartition.lean` gives the diagonal/off-diagonal decomposition for any countable index type and arbitrary pair weight; model-specific uses remain with their probability or branching-process owners |
| Deterministic finite range, corridor, and feedback bounds | `Order/Bounds` | `Truncation` provides the reusable finite event-tail decomposition; `Feedback` gives endpoint, within-block, and real scaled-window bounds; `RangeCover` covers a unit-range tube by finitely many uniform corridors; `FiniteRangeTranslation` translates any nonempty finite family of pairwise diameter at most `w` into `[0,w]`; `Corridor` gives a generic one-jump path estimate. Each statement is an order/algebra interface used by path or probability owners, with the truncation formula retained as a reusable finite-family tool. |
| Set extrema transported through order duality | `Order/OrderDual/SetExtrema` | The image equivalences for `toDual` and `ofDual` require only `LE`; Mathlib's corresponding duality lemmas require `Preorder` |
| Finite affine grids and rational interval coordinates | `Order/Interval` | `UniformGrid` defines finite affine subdivisions in ordered fields; `DyadicGrid` specializes them to nested powers of two; `RationalGrid` represents finite rational families on such grids; `RationalCoordinate/UnitInterval` owns the rational subtype of $[0,1]$ |
| Lower-set restriction of set-valued families | `Order/SetDissipate` | `Set.dissipate_congr` extends Mathlib's `Set.dissipate`: if two families agree for every $y\leq x$, their dissipations at $x$ agree; the result requires only `[LE α]`, so it also applies beyond natural-indexed sequences |
| Dense rational and dyadic coordinates on the real unit interval | `Topology/Order` | `UnitInterval/Rational` embeds rational coordinates into the real unit interval and proves dense range; `DyadicUnitInterval` gives the countable dense union of finite dyadic grids |
| Càdlàg paths, oscillation, jumps, range constraints, and uniform limits | `Topology/Cadlag` | `Basic` owns the path structure; `Oscillation` gives local one-sided variation bounds; `Jump` proves finiteness of jumps above a threshold and countability of discontinuities; `Range` defines path-range constraints and `IsCadlag.range_subset_of_dense` extends closed range bounds from a dense time set containing $\top$; `UniformLimit` proves closure under uniform limits into complete pseudo-metric state spaces. These are path-space interfaces, not proof-chain lemmas. |
| Skorokhod compactness and separability | `Topology/Cadlag/Skorokhod/Compactness` and `Topology/Cadlag/Skorokhod/Path/Separable` | `Compactness/MovingPartition` owns the reusable compact finite-parameter family of step paths with moving knots and its approximation-membership interface; `Path/Separable` owns the public countable-dense-set theorem and separability instance. The explicit countable parameter-family construction remains in `Path/Lemmas/Separable`. The finite family supports multiple compactness and separability clients, so it is not proof-only. Mathlib supplies compactness and separability primitives, but not these J₁ path-space interfaces. |
| Skorokhod oscillation tubes, finite oscillation partitions, and double-excursion criteria | `Topology/Cadlag/Skorokhod/Oscillation` | `Basic` specializes `Metric.OscillationBounded` to path oscillation and owns its open and closed tubes; `Dense` gives the countable rational-coordinate descriptions; `Partition` owns finite partitions, cellwise bounds, step approximations, time-change pullback, measurability, and existence for càdlàg paths. `DoubleExcursion/Basic` and `DoubleExcursion/Converse` give the partition-to-modulus and modulus-to-partition implications. The one-use jump-location, jump-separation, and oscillation estimates live under `DoubleExcursion/Lemmas/JumpControl`; converse-only construction details remain private to `DoubleExcursion/Converse`. The pathwise moduli correspond to Patrick Billingsley, *Convergence of Probability Measures*, 1st ed., Wiley, 1968, Chapter 3, §14, Theorem 14.4, p. 119; the formalized implications are stated for metric-valued paths. |
| Bounded metric cutoffs and pairwise range oscillation | `Topology/MetricSpace` | `Cutoff` defines $x\mapsto\min(1,\operatorname{dist}(x,s^c))$ and proves continuity, the $[0,1]$ bound, and positivity exactly on open $s$ when $s^c$ is nonempty. `Oscillation` defines the generic function-level bound `Metric.OscillationBounded` and identifies it with the extended diameter bound on `Set.range f` using Mathlib's `Metric.ediam`; path-space and random-walk modules reuse this predicate. |
| Linear paths in Skorokhod space | `Topology/Cadlag/Skorokhod/Path/Linear` | Reuses the canonical continuous map $t\mapsto at$ and owns its $J_1$ distance and uniform-error estimates; Brownian support arguments consume this path-space interface. |
| Terminal-left endpoint convention for càdlàg path spaces | `Topology/Cadlag/Skorokhod/Path/TerminalLeft` | `terminalLeftPath` and `terminalLeftPathSpace` define the modification $f(1)=f(1-)$ for arbitrary topological state spaces; the construction maps paths into the endpoint subspace when the state space is T₂. Borel measurability of the real-valued specialization belongs to `MeasureTheory/MeasurableSpace/CadlagPath/TerminalLeft`. |
| Affine parametrizations, unit-block time coordinates, and the named identity clock | `Topology/Order/UnitInterval/Time` | Reuses Mathlib's `unitInterval.toNNReal` and `Set.projIcc`; `unitInterval.toNNReal_top` supplies the maximal endpoint value not separately named by Mathlib, `unitInterval.exists_mul_eq` and `exists_add_mul_eq` parametrize nonnegative and translated nonnegative intervals, `unitInterval.blockParameter` projects time into its unit block and sums to elapsed time, and `unitInterval.clock` names the identity coordinate used as a process clock |
| Càdlàg floor maps and limits from convergent order bounds | `Topology/Order` | `FloorCadlag` proves the integer- and natural-valued real floor maps are càdlàg; `Limit` gives the order-topological two-index squeeze result when every fixed approximant converges and the approximating limits converge to the same value |
| Extended-real limit rules for real-valued functions | `Order/EReal` | `LiminfLimsup` states arbitrary-filter translation and vanishing-perturbation formulas for `EReal` limsup and liminf; multiplicative scaling uses Mathlib's `EReal.limsup_const_mul_of_nonneg_of_ne_top` and `EReal.liminf_const_mul_of_nonneg_of_ne_top` directly |
| General filter limits and slow diagonal selection | `Order/Filter` | `LiminfLimsup` identifies bounded limsups and liminfs under a vanishing difference for densely ordered, conditionally complete topological additive groups with continuous addition and negation; `SlowDiagonal` selects monotone $d_n\to\infty$ with $P(d_n,n)$ eventually from eventual validity for each fixed parameter. Quantitative real-sequence error constraints belong to `Analysis/Asymptotics/Sequence/SlowDiagonal` |
| Finite ordered-family range translations | `Order/Bounds` | `FiniteRangeTranslation` places values of `x:ι→G` on any nonempty finite set `s⊆ι` inside `[0,w]` in a linearly ordered additive group, provided `|xᵢ−xⱼ|≤w` for all `i,j∈s` |
| Deterministic process-time grids and rounding time functionals up to grids | `Probability/Process/TimeGrid` | `UnitInterval`, `Expanding`, `Dense/NonnegativeRationals`, `Ceiling`; the ceiling selector specializes Mathlib's `MeasureTheory.hittingBtwn` and its convergence theorem is independent of paths and probability laws |
| Balanced finite block-length lists | `Combinatorics/Sequence/BalancedPartition` | Given a total horizon $N$ and reference length $r$, constructs $q=\lfloor N/r\rfloor$ near-equal natural-number block lengths whose sum is exactly $N$; each length is one of the two adjacent integers around $N/q$. Mathlib's `List.splitLengths` consumes an already supplied length list, while this constructor creates the balanced list from quotient and remainder data. |
| Finite sequence blocks and variable-length block starts | `Combinatorics/Sequence/Block` | Defines a length-`ℓ` window of any sequence, its default-padded form, and the prefix-sum start index for an arbitrary sequence of natural block lengths. These combinatorial interfaces are reused by additive-path and finite IID block constructions; the additive displacement identities live beside `AdditivePath`. |
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
| Generic compact-system products and closure operations | `Topology/Compactness/CompactSystem/Operations` | Extends Mathlib's `IsCompactSystem` with products, countable intersections, finite unions, and finite intersections; these results do not depend on analytic sets or capacities |
| Analytic-set projections, pavings, and capacities | `MeasureTheory/Analytic` | `Projection` owns continuous images and coordinate projections of Borel sets in Polish spaces; `Paving/` owns paving-analytic sets and their projections; `Capacity/` gives the cited capacitability theorem |
| Measure operations, product estimates, and invariance under limits | `MeasureTheory/Measure`, `MeasureTheory/Integral`, and `MeasureTheory/OuterMeasure` | `Measure/Convolution/Power`, `Measure/Algebra/{DiracSum,FiniteProduct,IntegerValued}`, `Measure/InnerMeasure`, `Measure/EventLimits`, `Measure/Convergence/MapInvariance`, `Measure/Pi/FiniteReindexCover`, `Integral/MeasurePreserving`, `Integral/Lebesgue/RestrictLimit`, and `OuterMeasure/Finite/Cover` |
| Measurable finite partial sums | `MeasureTheory/Function` | `FinPartialSum` proves measurability of every finite partial-sum coordinate for a measurable additive monoid, without a topology assumption |
| Real Gaussian interval, sign, moment, and finite-product facts | `Probability/Distributions/Gaussian` | `Interval` gives positivity of nonempty open intervals and strict CDF bounds at zero; `Sign` gives half-line probabilities and their variance scaling; `FourthMoment` gives finiteness and variance scaling of the fourth absolute moment; `FiniteProduct` gives positivity and scale monotonicity of products of interval masses. These distribution-level interfaces remain independent of random-walk and Brownian applications. |
| Rademacher and scalar-rescaled real distributions | `Probability/Distributions` | `Rademacher.lean` owns the two-point law, Boolean encoding, pushforward identity, and its integral and truncated-second-moment formulas; `Scaling.lean` owns the general positive-dilation identity $F_{rX}(x)=F_X(x/r)$ for every real threshold. Neither depends on a random-walk path model. |
| Logarithmic comparison for finite probability products | `Probability/MeasureTheory/FiniteProduct` | Converts a finite ENNReal product bound on measurable-event probabilities to the corresponding real logarithmic-sum inequality, in both inequality directions, under the precise positivity conditions needed by `toReal` and `log`. |
| Asymptotic probability rates and small-deviation scales | `Probability/MeasureTheory/Asymptotics` | `LogarithmicRate` gives generic transfers from finite products of exponential lower bounds and eventual power upper bounds to normalized logarithmic rates; `SmallDeviation` defines a scalar power-law small-deviation property and proves its radius-rescaling rule. The Mogul'skii application remains in the stable-process small-deviation module. |
| Positive-probability sublevel events from first-moment bounds | `Probability/MeasureTheory/SmallValue` | `Basic.lean` proves that a measurable nonnegative ENNReal-valued random variable with expectation below $ρ$ is below $ρ$ with positive probability. The one-use Campbell adapter was removed; Poisson applications combine this result directly with the generic restricted-integral limit. |
| Measurable continuous-path range constraints | `MeasureTheory/MeasurableSpace/ContinuousMap` | `Oscillation` makes the bounded range-diameter and zero-start subsets of continuous paths measurable |
| Lévy measures on the real line | `MeasureTheory/Measure/Levy` | `Basic` defines `IsLevyMeasure`; `Scaling` proves stability under nonzero dilation; `Cutoff` owns the canonical small/large-jump split; `AtomFreeRadii` gives a null-sphere radius in every positive interval and a sequence of such radii tending to zero |
| One-sided tail thresholds and capped first moments | `MeasureTheory/Measure/Tails` | `Positive` turns positive mass on $(0,\infty)$ into a positive strict-tail threshold; `Power` integrates a two-sided tail bound $\nu(|x|>t)\le Ct^{-\alpha}$ with $\alpha<1$ to obtain $\int\min(R,|x|)\,d\nu<\infty$ |
| Measurable optional values | `MeasureTheory/MeasurableSpace/Option` | the disjoint-union measurable structure on `Option X`, measurability of `some`, `Option.map`, `getD`, and `elim`, and measurable presence events |
| Measurable filtering of finite-valued maps | `MeasureTheory/MeasurableSpace/Finset` | `Filter` proves that a measurable `Finset`-valued map stays measurable after a pointwise measurable, parameter-dependent filter; branching-step rules use this general result |
| Finite measure families, summable atom levels, and finite-partition bounds | `MeasureTheory/Measure/Finite` | `OnFamily` defines finiteness on an arbitrary family and its compact/one-sided ray instances; `Domination` derives a.e. family finiteness from an integrable dominating functional; `AtomFiniteness` derives finite threshold sets and leftmost atoms from summable weights; `Partition` gives a finite disjoint-cell measure lower bound |
| Compact-range bounds and tightness for càdlàg path laws | `MeasureTheory/Measure/CadlagPath/Tightness` | `exists_eventually_compactRange_bound_of_real_error` converts compact-range probability estimates from real errors to arbitrary positive `ENNReal` errors for any filter of path laws; the tightness criteria combine common compact-range and oscillation-partition bounds, including eventual versions |
| Probability-law convergence and independence under weak limits | `Probability/ConvergenceInDistribution` | `Basic`, `Mapping`, and `Independence` cover convergence compatibility, continuous maps, and both directions of finite product/independence limits |
| Closed range constraints under weak convergence of càdlàg paths | `Probability/ConvergenceInDistribution/CadlagPath/RangeOscillation` | `limsup_measure_rangeOscillationLe_le_of_scalePath` combines closed-set Portmanteau with positive path scaling and the deterministic range-to-open-tube inclusion; it applies to arbitrary path-valued random variables and zero-start limiting laws, alongside the finite-dimensional càdlàg path limit interfaces |
| Moment convergence from probability-tail bounds | `Probability/MeasureTheory/Convergence` | `L2FromTails`, `L2FromVaryingTails`, and `L2FromPolynomialTails` give second-moment convergence under distinct fixed-law, varying-law, and polynomial-tail hypotheses; `L2Norm` transfers it to $L^2$ and variance; `TailExpectation` gives a one-sided first-moment bound |
| Moment inequalities and exponential-moment consequences | `Probability/MeasureTheory/Moments` | `PaleyZygmund.lean` gives the probability-space second-moment lower bound and its ENNReal support form; `ExponentialMoment.lean` derives fourth-moment integrability of the negative part from a finite exponential moment. The geometric-recursion consequence remains in `SecondMomentGrowth.lean`. |
| Moving-level-set and second-moment tail integrals | `Probability/MeasureTheory/Convergence/IndicatorTail` and `Probability/MeasureTheory/Moments/SecondMomentTail` | The first gives the general dominated-convergence consequence $\int 1_{\{a_n\leq f\}}f\,d\mu\to0$ for integrable $f\geq0$ and $a_n\to\infty$; the second gives the real second-moment bound $a^2\mu(|x|\geq a)\leq\int 1_{\{a^2\leq x^2\}}x^2\,d\mu$. Both serve multiple path-level applications and therefore belong in the measure-theory layer. |
| Probability lower bounds from geometric second-moment recurrences | `Probability/MeasureTheory/Moments/SecondMomentGrowth` | Bounds $M_n/\rho^{2n}$ when $M_{n+1}=\rho^2M_n+v\rho^n$, then combines the bound with Paley--Zygmund for any nonnegative square-integrable random-variable sequence with mean $\rho^n$; branching-process-specific recurrences remain with their model. |
| Measurable counting-measure processes | `Probability/PointProcess` | `PointProcess` bundles a measurable map into Mathlib `Measure` with integer-valuedness and the chosen finite-on-family condition |
| Exponential tilts of random-measure laws | `Probability/RandomMeasure` | `ExponentialTilt` weights any measure by $e^{\theta F}$, maps the weighted measure through a measurable potential, and mixes the resulting laws; no counting-measure or point-process hypothesis is imposed |
| Poisson distribution moments and marked-event positivity | `Probability/Distributions/Poisson` | `Moments.lean` gives the first, second factorial, and ordinary second moments, variance, corresponding integrals, and the zero-rate law; `MarkedEvents.lean` combines a Poisson count or marked count with an independent small-residual event. Mathlib owns the Poisson law, its normalization, and the convolution theorem; these modules provide moment formulas and complete event estimates not present in that interface. |
| Poisson random measures and marked point-family laws | `Probability/RandomMeasure/Poisson` | `RandomMeasure/` owns finite random-measure observations and their laws; `PointFamily/Basic` owns finite atom families, their measurable realizations, and the coordinate-to-piece index; `PointFamily/Independence` derives independence of disjoint coordinate blocks; `Integration/` and `Integrability/` own their integral interfaces; `Intensity/` owns product-intensity identities; `JumpPath/Basic` defines a cumulative marked-jump path and its one-point representation, `Bound` and `SmallVariation` give its variation estimates, and `JumpPath/Entrance/` gives the general two-source corridor-entrance model; `Realization/` provides its point-family constructions; `CharacteristicFunction/` and `Superposition.lean` own law-level characteristic-function and addition results. Mathlib's `poissonMeasure` is the Poisson distribution on $\mathbb N$ and its count-law API, rather than a marked random-measure construction, so this richer point-family interface stays in the project layer; see the [Mathlib Poisson API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Poisson/Basic.html). |
| Cutoff paths for Lévy Poisson configurations | `Probability/Process/Levy/Jump/PoissonConfiguration` | `Path.lean` identifies the canonical entrance path with its cutoff version and proves its almost-sure zero start; `Endpoint.lean` identifies the terminal jump sum; `Increment.lean` gives cumulative-integral and half-open time-window formulas. The generic single-jump path and two-source corridor-entrance construction are owned by `Probability/RandomMeasure/Poisson/JumpPath`; this directory keeps the identities that depend on Lévy cutoff bands. |
| Lévy-process semantics and Brownian adapter | `Probability/Process/Levy` | `Basic.lean` defines the process interface through zero start, independent stationary increments, and almost-sure càdlàg paths; `Brownian.lean` proves Mathlib's real Brownian motion satisfies that interface without making the general definition depend on Brownian-specific assumptions. |
| Three-dimensional Bessel radial path law | `Probability/Process/Brownian/Bessel` | `ThreeDimensional.lean` constructs the product law, radial process, and path law; `Endpoint.lean` proves endpoint positivity; `Support.lean` proves support for every nonnegative linear path. The complete radial perturbation estimate remains public in `ProbabilityTheory.BrownianBessel3` as the reusable coordinatewise interface used to prove the support theorem. The package cites J.-P. Imhof, “Density factorizations for Brownian motion, meander and the three-dimensional Bessel process, and applications,” *Journal of Applied Probability* 21(3) (1984), 500–510, Theorem 1, DOI 10.2307/3213612. |
| Standard Gaussian Brownian witnesses and continuous modifications | `Probability/Process/Brownian/Construction` | `Existence.lean` obtains a pre-Brownian and continuous Brownian witness on the path-block space used by random-walk functional-limit results; `KolmogorovMoment.lean` gives the fourth-moment Kolmogorov bound for every `IsPreBrownianReal` process; `PreBrownianModification.lean` supplies its selected measurable, pathwise-continuous modification. Mathlib owns the Brownian process predicates, and the buildable BrownianMotion Kolmogorov–Chentsov theorem supplies the general modification result. The canonical BrownianMotion process construction is not currently importable with the pinned dependency because its transitive targets fail to build, so the repository's tight-source construction remains the local owner. |
| Markov processes and chains | `Probability/Process/Markov` | `Basic.lean` states the conditional-expectation Markov property using Mathlib kernels, separates transition-family composition from the process property, and derives the discrete-time kernel-power specialization; `Stopping/Basic.lean` defines the finite-stopping-time strong Markov property and proves that a discrete-time Markov chain satisfies it. |
| First-declaration stopping times and their independent-event law | `Probability/Process/HittingTime` | `Declarations.lean` presents Mathlib's `hittingAfter` as an event-indexed first-success time, with finite-time, exact-time, one-generation-shift, and stopping-time laws; `Geometric.lean` proves the measurable fibers and geometric mass formula $\mathbb P(\tau=k)=p(1-p)^k$ for independent events of common probability $p$; `ObservableCandidates.lean` gives a filtration-generic interface for candidate completion observability, countable candidate unions, and first successful completion times. `Examples/Lookahead.lean` contains finite-filtration counterexamples illustrating the adaptedness hypotheses. The official [Mathlib hitting-time API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/HittingTime.html) supplies the underlying process hitting time and adapted stopping-time theorem; its [independent-event API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html) supplies finite intersection products, while the event-indexed presentation and geometric first-success law are additional reusable results. |
| Process corridor events, range, and block-return bounds | `Probability/Process/Corridor` | `Segment.lean` owns the process segment increment, full-segment corridor and endpoint events, and their pathwise inclusion/monotonicity algebra; `Range.lean` relates rational-coordinate range events to complete-segment corridors and their finite cover; `CoreReturn.lean` groups the two related power recurrences for prefix corridors, specializing the generic finite measure recurrence to the corridor events consumed by stable small-deviation estimates. Càdlàg rational-coordinate characterizations and null-measurability stay in `Probability/Process/Path/Skorokhod/Corridor/Segment.lean`. |
| Path-space geometry, path-valued realizations, and generic tightness criteria | `Topology` and `Probability/Process/Path` | `Topology/Cadlag/Skorokhod` owns the path space, $J_1$ metric, time changes, and deterministic corridor and oscillation events. `Probability/Process/Path/Representation` turns coordinate processes into continuous or càdlàg path-valued maps and their image laws; `FirstPassage`, `Extrema`, `Reflection`, and `TimeReversal` own the corresponding deterministic path transformations; `Skorokhod` and `PathClass/StepCorridor` connect those path objects to measurable tube events. These build on Mathlib's `CadlagPath`, continuous-map Borel structure, and `hittingBtwn`; the continuous-path and rational-coordinate corridor interfaces are not supplied by those APIs. See the [Mathlib càdlàg order API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Order/Cadlag.html) and [hitting-time API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/HittingTime.html). |
| Skorokhod time changes and finite-partition clocks | `Topology/Cadlag/Skorokhod/TimeChange` | `Basic` owns the general time-change object as an `OrderIso` of `[0,1]` and derives its homeomorphism from the order topology; `LogDistortion` owns secant-slope and composition bounds; `FinitePartition` constructs the piecewise-affine knot-matching clock and its path/log-distortion consequences. `Limit/Convergence` gives the continuous-map uniform limit of cumulative clocks under a summable distortion budget; `Limit/Strict` upgrades it to a time change; `Limit/LogDistortion` proves stability of the distortion bound; `Limit/Tail` constructs tail limits and factors the global limit through each finite prefix. These are independently stated convergence interfaces, while the one-use estimates stay private in their proof modules. The single-use secant-slope estimate belongs in `FinitePartition/Lemmas/SecantSlope.lean`. |
| Strict Skorokhod corridors and their continuous weights | `Topology/Cadlag/Skorokhod/Corridor` | `Basic` owns open and closed path corridors and their $J_1$ topology; `Endpoint` adds terminal windows; `Dense` identifies rational-coordinate events with full-path corridors and proves their product-space measurability; `Upper` owns the one-sided open corridor; `Weight` specializes the generic metric cutoff to these path events. The unused prefix/remainder gluing interface was removed because it had no importers or named callers. |
| Skorokhod `J₁` and Billingsley logarithmic path metrics | `Topology/Cadlag/Skorokhod/EDistance` | `Basic` owns the pseudometric-level uniform and `J₁` extended-distance formulas; `Logarithmic/` defines Billingsley's cost, proves separation and topology equivalence, and records the quantitative conversion modulus. `Logarithmic/Completion/Completeness` is the public completeness entry point; generic summable path alignment remains in `AlignedCauchy`, while the Billingsley-specific subsequence extraction and aligned-limit assembly are grouped under the single `Completion/Lemmas/` subtree as package-private declarations. The unused tail-sum wrapper and one-use alignment steps are removed from the public API. Clock changes and their distortion remain in `TimeChange/`. |
| Finite step-corridor endpoint cores and inner-cell geometry | `Topology/Cadlag/Skorokhod/PathClass/StepCorridor/Partition` | `LowerCores` selects knot cores; `LowerGeometry` places finite real bounds in the common cells, without assumptions on a probability law |
| Finite step-corridor classes and continuous-boundary approximations | `Topology/Cadlag/Skorokhod/PathClass/StepCorridor` | `Boundary/Basic` defines finite right-continuous extended-real boundaries and their traces; `Boundary/Partition` owns the common finite knot partition; `Basic` defines the M₁/M₂ path classes and the continuous-admissibility criterion; `ContinuousBoundary` and `UniformGrid` give the continuous-boundary sandwich; `TerminalWindow` constructs the concrete one-terminal-jump unit tube. These deterministic path objects stay in topology; energy and probability consequences belong to their measure and process owners. |
| IID sequence laws, filtrations, and independence | `Probability/Sequence` | `Sequence/Block` owns finite-block coordinates and the measurable finite-block extension along `Fin.val` using Mathlib's `Function.extend`; `Sequence/IID/Basic` owns `iidSequenceLaw`, its finite-block product-law interface, and coordinate independence; stopping-time factorization remains in `Sequence/IID/StoppingTime` |
| Geometric rewards along an IID trial sequence | `Probability/Sequence/IID/GeometricReward` | `Definitions.lean` owns the failed-prefix event and reward summand; `FirstMoment.lean` gives the exact IID first-moment identity and its failure-only and split-cycle consequences; `ExponentialTransform.lean` gives the ENNReal failure-cycle transform. The formulas apply to arbitrary measurable IID marks and rewards, and complement Mathlib's geometric waiting-time law. The one-use finite-prefix factorization steps are package-internal under `Lemmas/FailurePrefix.lean`. |
| Finite random-walk path events | `Probability/Process/RandomWalk/Path/Event` and `Path/Survival` | `Drawdown` owns finite-history drawdown and endpoint events with measurability; `Oscillation` owns the pairwise range-oscillation event, its measurability and increment-law probability, and horizon monotonicity; `LastSignChange` owns the terminal one-sign segment and its measurable start index. `Path/Survival/Basic` owns finite and infinite nonnegative-survival events, including the general measurable finite-partial-sum event for an additive monoid with a preorder. Short structural properties stay in their defining semantic modules rather than getting one-lemma files. |
| Random-walk path corridors and horizontal-tube events | `Probability/Process/RandomWalk/Path/Corridor` | `Basic` owns open and closed corridor predicates on arbitrary time sets and their deterministic inclusions; `Horizontal/Basic` defines finite horizontal-tube events and their interval, reflection, rescaling, and width relations; `Horizontal/Core` adds measurability and IID probability interfaces; `Horizontal/StepPath` identifies those events with constant corridors for normalized step paths and transfers measurability; `Interpolation/Basic` proves the deterministic grid-vertex characterization of polygonal paths, and `Interpolation/Core` transfers it to the canonical IID path law. The continuous-path interval corridor itself is owned by `Topology/ContinuousMap/Corridor`. |
| Random-walk fluctuation and cyclic-survival estimates | `Probability/Process/RandomWalk/Fluctuation/SparreAndersen` | `Rotation/Cover` states the finite path cover; `Rotation/Basic` owns cyclic-survival events and their event identities and measurability; `Rotation/FiniteProduct` owns IID finite-product invariance and the endpoint-to-survival inequality; `Rotation/Probability` transfers that inequality to `iidSequenceLaw`; `Composition/InclusionExclusion` states the alternating-sum formula, with adjacent-block and gap-factorization proof steps under `Composition/Lemmas/BlockProbability/`. The generic product-measure reindexing uses Mathlib's `Measure.pi_map_piCongrLeft` API. |
| Drawdown events and small-deviation estimates | `Probability/Process/RandomWalk/SmallDeviation/Drawdown` | `Event.lean` owns $B_{L,\Delta,r}=\{S_i-S_j\leq\Delta\ (i\leq j\leq L),\ S_L\leq r\}$ and deterministic corridor consequences; `Scaling.lean` gives measurability and positive-rescaling identities. The finite-variance upper estimate is in `FiniteVarianceUpper/Theorems.lean`; its rounded-maximum, jump-pattern, conditional-block, and rate calculations, including the proof-specific block tube event, remain in `FiniteVarianceUpper/Lemmas/`. |
| Finite random-walk path windows | `Probability/Process/RandomWalk/Path/Window` | `Basic` owns deterministic finite-window and interval constraints with translation, block-coordinate, restart, and interval-shrinkage identities; `Core` owns measurability and the event indicator; `Endpoint` adds a terminal interval condition and its finite-block measurability interface. These related statements form module-level APIs, not separate files per lemma. |
| Random-walk polygonal paths and finite survival windows | `Probability/Process/RandomWalk/Path/Interpolation` and `Path/Survival` | `Interpolation/Basic` defines the normalized weighted-sum path and its pathwise identities; `Core` owns its continuous and càdlàg laws; `Finite/Lemmas/Grid` keeps one-use endpoint-estimate steps internal; `Limit` owns distributional transfers; and `Survival/Interpolation` identifies eligible polygonal windows with discrete block survival. |
| Maximal increments and interpolation error | `Probability/Process/RandomWalk/Path/MaximalJump` and `Path/Interpolation/Path/Approximation` | `MaximalJump/Basic` owns the finite maximum of absolute increments, its pointwise bounds, and measurability; `FiniteVariance` gives the IID union bound and the finite-second-moment diffusive negligibility result. `Interpolation/Path/Approximation` uses that result to compare step and polygonal paths in the Skorokhod metric. The measure-generic tail estimates are owned by `Probability/MeasureTheory`, rather than nested under interpolation. |
| Couplings of probability measures and order comparison | `Probability/Coupling` | `Basic` defines a joint measure with prescribed marginals and its common-variable, product, swap, and map constructions; `Order` compares preimage probabilities for every measurable upper set under an almost-sure order; `Tail` specializes this to real upper tails |
| Adaptive event selection from independent variables | `Probability/Independence/AdaptiveChoice` | Finite disjoint past cells select measurable events of an independent future variable; binary choice and its finite-step iteration are derived from the finite-choice bound |
| General random-walk process laws and paths | `Probability/Process/RandomWalk` | path maps, kernels, Donsker and small-deviation interfaces |
| Normal random-walk limits and Donsker's theorem | `Probability/Process/RandomWalk/FunctionalLimit/Normal` and `.../Donsker` | `Normal/FiniteDimensional/CentralLimitTheorem` identifies the canonical IID walk with Mathlib's scalar CLT and gives its interval Portmanteau bounds; `Normal/PathLimit/Basic` and `Brownian` state the Gaussian-domain path limits; `Normal/PathLimit/LinearTube` derives positive lower bounds for open $J_1$ balls around linear paths, including finite-variance and compact-slope forms; `Donsker/FiniteDimensional/Basic`, `Brownian`, `Grid`, and `Rational` progress from block-sum limits to Brownian endpoints, polygonal grid evaluations, and rational finite-dimensional limits; each stage publicly imports the objects in its theorem statements and ordinarily imports the preceding proof stage; `Donsker/Tightness/Path` exposes the oscillation estimate, explicit uniform path bound, and resulting tightness theorem, with its deterministic parameter choice under `Tightness/Lemmas/Parameters`; `Donsker/Path/Continuous` directly exposes its path, Brownian-process, IID-law, and convergence types, while importing rational finite-dimensional convergence and tightness as proof support; `Donsker/Path/` proves the continuous-path and Skorokhod invariance principles and groups the functional-limit corridor-to-tube adapters; `Donsker/Corridor/Brownian/Basic` gives open/closed Brownian corridor bounds, while `Endpoint` handles endpoint-constrained and scaled centered-tube consequences; entrance estimates remain under their semantic subdirectories |
| Conditioned random-walk first-window limit | `Probability/Process/RandomWalk/FunctionalLimit/Conditioned/FirstWindow` | `Existence` proves almost-sure existence of a finite surviving window; `BlockLaw` proves the selected finite block has the survival-conditioned law; `Selection` identifies the selected index and rebased path law; `Limit` proves convergence to the centered Brownian first-window path. Bolthausen-specific prefix events, block factorization, and finite-horizon convergence steps are grouped under `FirstWindow/Lemmas/`. Brownian first-window path operations are owned by `Probability/Process/Path/AboveStart`, and the separate meander-law identification is owned by `Probability/Process/Brownian/Meander/`. |
| Finite paths relative to a restart schedule | `Probability/Process/Path/Restart` | `Basic.lean` defines the cutoff schedule and the generic finite-path relative-window predicate; `Measurability.lean` proves measurability under `MeasurableSub₂`; `Bounds.lean` gives the ordered additive endpoint estimate. `Probability/Process/RandomWalk/Path/Restart/Windows.lean` connects that event to additive-increment histories; `Basic.lean` assigns its probability and proves initial-position invariance; `Interval.lean` gives the IID closed-interval factorization; `Corridor.lean` specializes it to horizontal tubes. The interval-specific block-event calculation used only in that proof is under `Lemmas/IntervalFactorization.lean`, reusing the general variable-length IID block-event factorization. |
| IID random-walk block maximal estimates | `Probability/Process/RandomWalk/Path/Block/Maximal` | `Basic` specializes Mathlib’s Doob maximal inequality to deterministic IID increment blocks; `SecondMoment` states the centered unit-second-moment squared-maximal estimate, its absolute-value event form, the finite-scale ratio bound, and its diverging-scale consequence. The event statements are reused in block partitions, Donsker tightness, and corridor comparisons. |
| Random-walk block corridors and second-moment comparisons | `Probability/Process/RandomWalk/Path/Block/Corridor` | `Core` gives the distribution-free starting-margin/corridor comparison; `SecondMoment` adds the finite-variance error and a uniform diffusive-block version for every diverging scale under unit second moment. It composes the project’s IID block maximal estimate with the generic corridor inclusion. Mathlib’s [`MeasureTheory.maximal_ineq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/OptionalStopping.html) is Doob’s maximal inequality for nonnegative submartingales; it supplies a process-level tool, while this module packages the IID random-walk event interface used by block arguments. |
| Random-walk partitions of step corridors | `Probability/Process/RandomWalk/Path/Block/Partition/StepCorridor` | For arbitrary step boundaries and IID real increments, gives floor-grid cell indices and lengths, the global-to-cell path constraint, and an upper bound by the product of selected-cell partial-sum range probabilities; uses the generic variable-length IID range-product theorem |
| Terminal-left partitions for normalized random-walk paths | `Probability/Process/RandomWalk/Path/Skorokhod/TerminalLeft/Partition` | `Basic.lean` defines the clipped source-knot index and terminal cell lengths; `CellBounds.lean` transfers a terminal-left corridor constraint to selected half-open cells and bounds its IID probability by their range-probability product. The hypotheses are finite step boundaries and an IID real increment law, with no stable-law or asymptotic-scale assumptions. Mogulskii-specific lower geometry and product assembly remain under `SmallDeviation/Mogulskii/Lemmas/TerminalLeft/Partition/`. |
| Mogul'skii small-deviation theorem entry | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Theorems.lean` | The sole direct Lean file at the Mogul'skii root is the import entry for the four original article theorems; it identifies the formalized interfaces for Theorems 1–3 and records that Theorem 4 remains unformalized. The sibling `Gaussian/`, `Stable/`, `Rate/`, `Scale/`, and `Path/` directories own mathematical interfaces; theorem-specific derivations stay under `Lemmas/`. Generic terminal-left partition bounds live with their path owner, and Mogulskii-specific lower geometry and product assembly remain under `Mogulskii/Lemmas/TerminalLeft/Partition/`. Within `Stable/Discrete/`, `EscapeRateLowerBound.lean` exposes the complete discrete endpoint-return transfer estimate from a stable-process escape rate; its positivity and real-log helpers remain under `Stable/Discrete/Lemmas/`. `Stable/Discrete/Partition/{EnergyUpper,Upper,Lower,Limit}` contains the finite-partition rate interfaces: upper estimates, lower estimates, and their exact-rate combination; the one-client endpoint-core block product proof is under `Partition/Lower/Lemmas/BridgeProduct.lean`. |
| Normal-domain discrete Mogul'skii rates | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Discrete/FromIncrementLaw/Normal` | `Normalization` constructs positive Gaussian norming inputs by changing a finite prefix while preserving eventual equality and the attraction limit; `Domain` packages the rate data from a normal-domain source; `FiniteVariance` specializes it to centered finite-variance increments; `ContinuousBoundary` exposes the continuous-boundary and finite-corridor rates; `HorizontalTube/{Basic,Scales,EndpointWindow}` gives the closed-tube core theorem and its scale and endpoint-window forms. The one-use terminal-left-to-horizontal-corridor conversion is under `HorizontalTube/Lemmas/EndpointWindowCorridor`. These modules are theorem interfaces at the normal-domain specialization layer, while comparison with the source proof remains partial for the rate derivation. |
| Mogul'skii diffusive scale specialization | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Scale` | `Basic.lean` defines $a_n\to\infty$ and $a_n/\sqrt n\to0$ as a specialization of `Asymptotics.IsSmallDeviationScale`. The standard $n^{1/4}$ witness is used only while proving the Gaussian escape coefficient and is derived there from the general power-scale theorem; no separate public witness module is retained. The floor-rounded block length $b_n=\lfloor c a_n^2\rfloor$ and its complete-block limits are owned by the scale-generic `Analysis/Asymptotics/Scale/Block/Diffusive.lean`. |
| Finite-boundary Mogul'skii rates | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Rate` | `Energy.lean` defines $H_\alpha(f,g)=\int_0^1(g(t)-f(t))^{-\alpha}\,dt$ and its algebraic identities. `Partition/Finite` gives the complete finite-Gaussian-reference lower-rate statements, while `Partition/Cover` gives a distinct interval-level sufficient-condition theorem; the one-use compact interval net is in `Partition/Lemmas/FiniteCover.lean` and reuses Mathlib’s totally bounded finite approximation. Step-corridor energies with extended-real boundaries remain in `MeasureTheory/Measure/CadlagPath/PathClass/StepCorridor/Energy.lean`. |
| Scalar domains of attraction for normalized i.i.d. sums | `Probability/Distributions/DomainOfAttraction` | `Basic` defines the centered normalized sum and fixed-normalization attraction predicate; `Normalization` transfers the limit under changing scales; `Block` handles varying block lengths; `Centering` derives zero mean from uncentered attraction; `CharacteristicFunction` gives the finite-sum transform and its limiting consequences |
| Variable-length random-walk block paths | `Probability/Process/RandomWalk/FunctionalLimit/NormalizedStep/Block` | `normalizedStepBlockCadlagPathIcc` and its law encode a block with independently varying time and space scales; weak-limit bounds for the resulting path events belong to `Probability/ConvergenceInDistribution` |
| Rademacher finite-interval paths, range events, and tube spectrum | `Probability/Process/RandomWalk/Rademacher/FiniteInterval` | `Path`, `KilledKernel`, `Matrix`, and `Scale` define the finite killed walk; `Range/` identifies lattice paths and gives range and corridor-survival bounds; `Spectral/` owns the sine basis, survival estimates, and terminal-target analysis. The six modules in `Spectral/Target/` form the target-mass interface: coefficient, spectral expansion, extremal modes, lower bound, path interpretation, and diffusive limit. `Spectral/Survival/Asymptotics/CenteredTube` gives centered-tube limits for arbitrary radii and real spatial scales. |
| Finite-horizon kernel survival, returns, and bridges | `Probability/Kernel/Survival` | remaining mass, restriction to measurable cores, variable return-block sequences, final bridges, and sub-eigenfunction bounds |
| Markov-kernel powers | `Probability/Kernel/Markov.lean` | `IsMarkovKernel.pow` proves that every natural power of a Markov kernel remains a Markov kernel; it is the general kernel-level closure fact used by discrete Markov-chain transitions |
| Brownian corridor and range probabilities, and random-walk horizontal-tube estimates | `Probability/Process/Brownian/SmallDeviation` and `Probability/Process/RandomWalk/SmallDeviation/HorizontalTube` | Brownian corridor masses and range small-width bounds; Donsker lower bounds for centered unit-variance horizontal tubes; logarithmic-rate transfer under positive rescaling of increments |
| Random-walk range and block-oscillation small deviations | `Probability/Process/RandomWalk/SmallDeviation/Range` | `IndependentBlocks` gives the finite-horizon IID range-to-block probability inequality; `BlockDonsker` transfers finite-block oscillation to Brownian range mass; `BlockOscillation` compares the block event with Mogul'skii's source corridor; `QuadraticEnergyCover` supplies the finite `M₃` corridor cover with exponent-two energy; `Rate` assembles the finite-variance rate. The generic arbitrary-index cover is owned by `Order/Bounds/RangeCover`, and its càdlàg-path adapter by `Topology/Cadlag/Skorokhod/SmallDeviation/RangeCover`. |
| Random-walk entrance and endpoint-corridor estimates | `Probability/Process/RandomWalk/SmallDeviation/Entrance` | `MovingCorridor.lean` owns the moving-boundary event. `NormalDomainEvent.lean` exposes the finite entrance events and their membership equivalence; `NormalDomain.lean` owns the normal-domain entrance probability bounds. Finite-variance middle-corridor and endpoint conclusions live under `FiniteVariance/`, with Donsker support grouped below `FiniteVariance/Lemmas/InteriorDiffusive/`. The robust event and exponent-uniform entrance bound cite Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring* (master's thesis, Fudan University, 2026), Appendix A.2, Lemma A.7 and Chapter 3, Lemma 3.5; their one-use proof chain stays under `Robust/Lemmas/`. The finite path, cyclic geometry, IID cover estimate, and path-law transfer for the normal-domain entrance proof are internal under `Lemmas/Rotation/`. General cyclic-sum identities remain at `Algebra/BigOperators/CyclicReindex.lean`, finite product-measure reindexing at `MeasureTheory/Measure/Pi/FiniteReindexCover.lean`, and the finite-horizon survival inequality at `Fluctuation/SparreAndersen/Rotation/Probability.lean`. The Donsker open-linear-ball lower bounds remain at `FunctionalLimit/Normal/PathLimit/LinearTube.lean`. |
| Stationary increment laws | `Probability/Process/StationaryIncrements` | `HasStationaryIncrements`; independent of independent-increment and path-regularity assumptions |
| Independent-increment process operations and laws | `Probability/Process/IndepIncrements` | `Basic` handles monotone time changes; `Disjoint` handles separated increments; `FiniteDimensional` reconstructs position laws and identifies translated process laws; `PathLaw/StationaryTimeChange` identifies centered path laws |
| Stable random-walk functional limits | `Probability/Process/RandomWalk/FunctionalLimit/Stable` | `Tightness/Result` proves the three centered-regime tightness criteria; `PathLaw/WalkGrid` and `EndpointGrid` identify finite-grid laws; `PathLaw/Subsequence` and `Process` construct subsequential stable path laws; `PathLaw/Convergence` proves the tightness-plus-grid-law convergence theorem; `PathLimit/RandomWalk` states the three index-regime invariance principles, and `PathLimit/Block` handles variable-length blocks |
| Stable random-walk path-law escape rates | `Probability/Process/RandomWalk/FunctionalLimit/Stable/PathLaw` | `Process` constructs a stable clock path law from tight normalized random-walk path laws; `EscapeRate` composes that construction with the stable-process tube-rate transfer, yielding $a^\alpha\log P(\mathrm{tube}(a))\to C<0$ under explicit domain-of-attraction, tightness, and sign hypotheses |
| Finite observation block independence | `Probability/Process/IndepIncrements/FiniteObservations` | `Grid` enumerates finite time sets; `BlockVectors` handles finite increment sums; `BlockPaths` proves independence for arbitrary queries in adjacent blocks; `DisjointPaths` extends this to path-valued processes. `Lemmas/Grid` holds the grid-index facts used by the block-path proof. |
| Stable-law and stable-process semantics | `Probability/Distributions/Stable` and `Probability/Process/Stable` | Stable distributions and clock-increment/Lévy-process semantics live at their respective owners; `Process/Stable/Brownian` identifies the exponent-two Gaussian case and its canonical unit-interval path law, using Mathlib's Brownian predicates and repository stable-process interfaces |
| Stable Poisson jump-model endpoint and increment laws | `Probability/Process/Stable/JumpModel` | `EndpointLaw` identifies the cutoff small-plus-large jump sum and entrance-path endpoint with the stable law, and gives its stable time-window increment law; finite-dimensional laws and the selected path increment specialization build on that interface |
| Stable-domain norming, characteristic-defect, and tail consequences | `Probability/Distributions/Stable/Attraction/NormingRatios` | `Index` proves norming ratios and divergence; `UniformDefect` and `RegularVariation` transfer attraction to small-frequency defects; `Tauberian` gives tail and truncated-moment consequences |
| Stable-domain norming factors, time scales, and block rescaling | `Probability/Distributions/Stable/Attraction/Norming` | `Basic` defines the truncated-moment factor, stable norming predicate, small-deviation rate, and inverse time scale; `Asymptotics/` owns the consequences for regular variation, centering, norming-scale tails, and block inversion; `Rescaling/` connects domain-of-attraction normalizations to Mogulskii's convention; `SpecialCases/` records Gaussian and index-two consequences |
| Gaussian domain of attraction and its truncated-moment consequences | `Probability/Distributions/Stable/Attraction/Normal` | `Basic` owns the finite-variance Gaussian attraction criterion and defect data; `CharacteristicTail` transfers the squared-modulus defect to increment tails; `QuadraticTail` proves Feller's quadratic-tail condition and slow variation for infinite-variance laws; `Centering` proves first-moment integrability and zero mean; `Norming` derives the characteristic-defect comparison, quadratic norming, and tail profiles. Generic discarded-first-moment estimates belong to `Probability/Distributions/Moments/Truncated/TailIntegral`. |
| Real moments, truncated second moments, and tail integrability | `Probability/Distributions/Moments` | `Real.lean` defines the measure-level centered second-moment condition and its scaling, reflection, positivity, and $L^2$ consequences; `Signs.lean` derives half-line mass and bounded increment windows under finite-measure assumptions; `Truncated/Basic` defines and controls the truncated second moment; `Truncated/Layercake`, `TailIntegral`, `TailAsymptotics`, and `RegularVariation` own its tail representations and asymptotic criteria; `TailIntegrability.lean` relates absolute moments and two-sided tails. General regular-variation theorems remain in `Analysis/Asymptotics`. |
| Subadditive ergodic cocycles and their limits | `Probability/Ergodic/Kingman` | `Basic` owns the cocycle interface, `EnvelopeInvariant` exposes the a.e.-invariant liminf envelope, and `Core` proves Kingman's a.e.-convergence theorem; theorem-specific stopping-time and envelope estimates remain under `Lemmas/` |
| Independence of stable paths on partition cells | `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Partition` | `Independence` exposes mutual independence of the spatially normalized cell paths under the stable clock law; the one-use event-product calculation stays private inside `Partition/Lower/Assembly` |
| Stable-process path-class rates on finite step-corridor partitions | `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor` | `Partition/Core` normalizes each cell under stable time-space scaling and bounds scaled corridor probabilities by products of stable tube probabilities; `Partition/Lower/Kernel` owns complete endpoint-return rate interfaces; `Partition/Lower/Rate` assembles fixed inner-partition lower bounds, with one-use core-shrink and geometry calculations under `Lower/Lemmas/`; `Partition/Upper/EnergyRate` gives the matching energy upper bound and exact `M₂` limit; `Rate` exposes the stable-process `M₂` and `M₃` entries |
| Stable-domain small-deviation blocks and complete-block counts | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Scale` | `BlockLength` owns the stable block length and its scale limits; `BlockCount` exposes the complete-horizon and segment-count limits, specializing the generic quotient/remainder API in `Analysis/Asymptotics/Scale/Block/`; the endpoint-core bridge count stays in `Stable/Discrete/Lemmas/Partition/BalancedCoreCount.lean` |
| Stable Mogulskii block corridors and one-block bounds | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Corridor` | owns the stable-length tube events and the source IID block-to-horizon estimates; its closed-range estimate applies the general theorem in `Probability/ConvergenceInDistribution/CadlagPath/RangeOscillation` |
| Power-law small-deviation asymptotics at zero | `Probability/MeasureTheory/Asymptotics` | `HasPowerLawSmallDeviationRate` records eventual positivity and the limit $\varepsilon^\alpha\log p(\varepsilon)\to C$ for any scalar function; `HasStableProcessEscapeRate` specializes it to stable path-tube probabilities in `Stable/SmallDeviation/EscapeRate/PathLaw/Basic` |
| Branching random-walk models, populations, and field coupling | `Probability/BranchingRandomWalk` | `Law.lean` names arbitrary probability laws on walk space; `IID.lean` constructs and transports the canonical product-field law; `Measurability.lean` owns coordinate and finite-survival measurability; `BranchingProperty.lean` gives the selected-subtree law. In `Walk/`, `Rademacher.lean` defines the singleton-slot Rademacher model and `Path/RademacherFiniteInterval.lean` identifies its finite closed-window event with the killed interval-kernel mass. `Population/` owns root-indexed and finite multi-root candidate generation and selected-process recursion; `Restart/RootedTrial/` owns reserve-spine and finite-slot couplings; offspring fields and spine remain at their respective semantic layers |
| Measurable ordering of random branching-step laws and first-child observations | `Probability/BranchingRandomWalk/Step/Ordering` | `Realization` defines the measurable ordered realization of one random step; `Field` defines the optional least-slot mark and its generation measurability; `Law` transports child laws and point-measure functionals; `Support` gives simultaneous almost-sure ordering, nonemptiness, and first-child survival. Whole-tree address transport remains under the deterministic `Combinatorics` layer |
| Finite step-selected branching populations and split-schedule trials | `Probability/BranchingRandomWalk/Population/Processes/StepSelection` | `Basic` owns the recursive selected population; `SelectedPath` defines edgewise selection and characterizes generation membership by path length and selected edges; `RootIndexed` adds root labels; `Concurrent/{Basic,Scheduled}` groups the global-clock population and its causal-schedule specialization; `SplitSchedule/Definition` owns threshold-triggered trial times and successful root extraction, `Field` owns fresh-pool/product-law and spatial-coupling interfaces, and `Trials` owns completion, iteration, and repeated-success results |
| Root-indexed and finite multi-root selected-population candidates | `Probability/BranchingRandomWalk/Population/Candidates` | `Prefix` and `RootIndexed/` define generic address-level child sets; `MultiRoot` and `Adapted` define the finite first-slot candidates and their causal measurability; `Ordering` defines the position/address key directly over `MultiRoot`; `Leftmost` gives fixed-pool ranking and measurability; `FullChildren` and `FullSelection` expose the full-child definitions and finite-to-full selection theorem. The ordered-sibling comparison used only by that theorem is under `Lemmas/FullSelection.lean`. |
| Root-indexed finite first-$N$ population recursion | `Probability/BranchingRandomWalk/Population/Processes/Selected` | `RootIndexed` defines the recursive process, `ParameterizedRootIndexed` gives the joint-measurability interface when the initial position vector is a variable, `Basic` proves adaptation and population bounds, and `GenerationUpdate` states invariance under generation-local field updates. The one-use child-set update identity stays private in `GenerationUpdate.lean`. |
| Root-indexed branching-field coupling | `Probability/BranchingRandomWalk/Coupling` | `Slice` links probabilistic couplings to pathwise cloud domination; `Field/Preimage`, `Field/Law`, and `Field/Adaptive` give random matching, fixed pasting, and predictable descendant-field splicing; `Field/Ranked/` owns recursive equal-rank fields and their measurability and law; `Field/Position` specializes to branching-walk positions; `Rank/` owns guarded inverse, generation/block maps, and fixed/adaptive product-law preservation |
| Root-indexed branching-field laws and event counts | `Probability/BranchingRandomWalk/Genealogy/RootIndexed` | `Law/Basic` owns the root product law and marginals; `Law/IndependentEventCount` owns the independent-root count and the reusable exact/exponential avoidance bounds for a measurable event in one root field |
| Fixed and adaptive root-indexed subtree fields | `Probability/BranchingRandomWalk/Genealogy/Exploration/RootIndexed/SelectedSubtrees` | `FixedFamily` owns deterministic reindexing and its future product law; `SelectedFamily` owns the law, event factorization, and independence for generation-measurable root choices; `Iteration`, `Coordinates`, and `Position` track repeated replacements and original locations; `Coupling` compares iterated populations spatially; `GenerationBatch` packages the offspring batch read at selected roots |
| BRW path laws, many-to-one results, path counts, and MRCA decomposition | `Probability/BranchingRandomWalk/Spine/Path` | `ManyToOne/Event` defines one-root history events; `ManyToOne/PathCount` gives path-count/event and moment interfaces; `SecondMoment/Basic` owns pathwise diagonal/off-diagonal and MRCA decompositions, while `SecondMoment/SubtreeLaws` owns distinct-child subtree laws and integrated second-moment identities, independent of corridor geometry and selection |
| BRW affine-tube histories, corridor events, and tube estimates | `Probability/BranchingRandomWalk/Spine/Tube` | `Corridor/Events` owns the affine-corridor sets and their reusable event properties; `MRCA/` owns ancestry-prefix factorizations and the depth-indexed affine-tube contribution, with depth zero covering the root split; `MRCA/ChildPairBound.lean` exposes the complete fixed-ancestor and integrated cross-child estimates for arbitrary measurable corridors, while its conditional many-to-one and weighted-series calculations remain in `MRCA/Lemmas/ChildPairBound.lean`; `Corridor/PairBound` and `Corridor/SecondMoment` own the corresponding pair and moment estimates |
| Selection mechanisms, including random rules | `Probability/BranchingRandomWalk/Selection` | `Random` defines arbitrary set-valued rules and capacity bounds; `Finite/` specializes to finite candidates and value ranking; `Causal`/`FiniteCausal` impose the domain flow; `Process` applies these rules to time-indexed populations; `Overflow` gives the capacity-exceedance stopping time; `Coupling/` compares selected populations with first-$N$ clouds |
| Deterministic first-`N` selection, speed, and tail estimates | `Probability/BranchingRandomWalk/Selection/NSelection` | `NSelection`, selected-population endpoint/drawdown bounds, and speed proof. `Law/SelectedPopulation.lean` is the product-law interface for the totalized first-`N` target; `Law/Causal/` groups the causal-population, arbitrary causal-selection, step-selection, restarted-window, and nested-root coupling specializations. Under `EndpointDeviation/SecondStage/`, `Tube.lean` owns the affine tube, all-root failure event, and one-root PZ ratio; `Population.lean` owns the restarted killed population and finite-slice theorem; `Roots/Population.lean` owns the restarted field/population types and threshold event; `Roots/Selection.lean` owns the predictable finite-slice root constructor and its measurable, injective-family interface. In `EndpointDeviation/Drawdown/Spine/`, `Window.lean` defines the restarted-window event used by the failure-probability statement, while `Lemmas/` holds the theorem-specific second-stage tube and its one-use probability/scale reductions. The one-use pathwise population transfer is in `Lemmas/PopulationTransfer.lean`; the predictable-root probability estimate and its finite-slice specialization form one proof chain in `Roots/Lemmas/AllAvoid.lean`. |

Directory names should follow the owning concept. A declaration is not moved
to a theorem-specific directory merely because that theorem currently uses it.
Conversely, a general-looking name does not justify a generic module if its
definition relies on stable, branching, or other model-specific hypotheses.
The `Selection` namespace is mechanism-neutral and can describe random or
deterministic rules. `NSelection` is the deterministic first-`N` specialization;
results about its selected population belong under `Selection/NSelection`, not
the generic `Selection` subtree. Position observation on a root-indexed field
is owned by `Genealogy/RootIndexed/Measurability`, independently of whichever
selection mechanism consumes it. BRW path-count identities and pair decompositions
by most recent common ancestor belong under `Spine/Path`; they describe the
genealogy underlying path correlations and do not depend on a corridor. The
random-walk small-deviation estimates used for corridors stay under
`Probability/Process/RandomWalk`, while their affine-tube application and
second-moment bounds stay under `Spine/Tube`. These are BRW results, not
N-BRW selection statements; the latter belong under `Selection/NSelection`.

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
the strict whole-path range bound is in `Range/IndependentBlocks.lean`.
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
strict range-event counterpart is in `Range/IndependentBlocks.lean`. The diffusive target-mass
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
in `Probability/Process/Path/AboveStart/RunningMinimum.lean`. For a continuous
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
interfaces in `MeasureTheory/Measure/Levy/Cutoff.lean`; the complex
compensation and uncompensated-integrand identities remain in
`LevyKhintchine/FiniteVariation.lean`. The literature gives a more general
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
for arbitrary uncountable subsets. The complete Lévy-specific selection of
radii with null spheres `{x | |x| = r}` is a reusable property of every Lévy
measure, so its two theorems live beside the Lévy-measure definition in
`MeasureTheory/Measure/Levy/AtomFreeRadii.lean`. They use the generic null-fiber
theorem and the finite-mass-on-annuli result from `LevelSet.lean` and
`Levy/Basic.lean`, respectively. The representation proof imports this
semantic interface rather than owning a local adapter.

This follows Mathlib's location guidance: the generic null-fiber result stays
in `MeasureTheory/Measure/LevelSet.lean`, while the complete property of a
Lévy measure stays beside `IsLevyMeasure`. The representation proof consumes
both interfaces without introducing a third, application-specific wrapper.

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

The root-indexed finite-rank selector at a stopping generation is owned by
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
the reserve spine and their source population;
Restart/RootedTrial/Coupling/ReserveSpine.lean compares that source with the
rank-installed first-N population;
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

Within `Restart/RootedTrial/Spine/`, `ReservePath.lean` owns the recursive
second-child reserve path, its lineage and causal-population interfaces;
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

## Initial-population speed transport

The generic finite order-statistic comparison by lower-tail counts belongs to
`Combinatorics/BranchingWalk/Selection/NSelection/Mechanism/AtRank.lean`, and
the value-preserving candidate-bijection theorem belongs to `Mechanism/Matching.lean`.
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

`Stable/Discrete/FromIncrementLaw/Normal/Normalization` and `Stable/Normalization` convert raw domain-of-attraction inputs into the Gaussian and stable Mogul'skii normalizations used by the source-facing rates. The stable rescaling and time reindexing depend on both the increment law and the Mogul'skii scale, so they stay under `FromIncrementLaw`; generic scale and stable-law operations remain in their respective analysis and probability modules. `FromIncrementLaw/Path/Realization` owns the complete arbitrary-i.i.d.-coordinate path-class rate record and its ordinary-probability consequence. `Path/ContinuousBoundary` and `Path/RealizationContinuousBoundary` provide complete continuous-boundary specializations for canonical and arbitrary i.i.d. realizations. The shared finite-corridor approximation and law-transfer tools are already owned by the path-class and sequence-law modules; no additional reusable abstraction is needed here.


## Mogul'skii equation-(34) bridge proof support

`Stable/Discrete/Bridge/Events` owns the source base-corridor and terminal-endpoint events with the original `(c,b]` convention. The supporting endpoint geometry, finite-center cover, entrance-mass comparison, endpoint-corridor decay, and logarithmic ratio are one-use stages grouped under `Bridge/Lemmas/`. Their finite block decomposition reuses `Path/Block/Corridor/FiniteBridge`, and entrance positivity reuses the stable entrance modules. This keeps semantic events public at their owner while proof-specific equation-(34) steps remain internal.


## Stable discrete endpoint estimates

`Stable/Discrete/Endpoint/BandTransfer/Rate` owns the public stable path-law endpoint-window estimates. `BandTransfer/Lower/CellBridge` owns the discrete endpoint-core return lower bound consumed by entrance and path-class partition results. `Endpoint/StablePathLaw`, `Endpoint/Upper`, and `Endpoint/StrictStable` expose separate lower, upper, and strict-attraction interfaces. Their proof-specific parameter, Portmanteau-transfer, seven-band iteration, and return-block assembly steps remain under the nested `Lemmas/` folders.

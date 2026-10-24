# Module ownership and abstraction boundaries

This document records where mathematical concepts belong and which Mathlib
objects the library builds on. It is intended to guide new definitions and
identify misplaced application-specific assumptions.

## Ownership map

| Concept | Owning layer | Existing interface or representative module |
| --- | --- | --- |
| Address trees and deterministic genealogy | `Combinatorics/UlamHarris` | `TreeNode`, `Tree`, `MarkedTree` |
| Optional child configurations and deterministic branching walks | `Combinatorics/BranchingWalk` | `Step`, `surviveAlong`, `BranchingWalk` |
| Additive paths and finite block sums | `Algebra/BigOperators` | `AdditivePath`, `AdditivePath/Block` |
| Order-only finite bounds and grid coordinates | `Order` | `Order/Bounds`, `Order/Interval/UniformGrid` |
| Deterministic process-time grids and rounding time functionals up to grids | `Probability/Process/TimeGrid` | `UnitInterval`, `Expanding`, `Dense/NonnegativeRationals`, `Ceiling`; the ceiling selector specializes Mathlib's `MeasureTheory.hittingBtwn` and its convergence theorem is independent of paths and probability laws |
| Deterministic asymptotic scales and limits | `Analysis/Asymptotics` | `Scale`, `InverseScale`, `BlockScale`, regular variation |
| Measure operations, integral limits, and invariance under limits | `MeasureTheory` | `Measure/Convolution/Power`, `Measure/DiracSum`, `Measure/Convergence/MapInvariance`, `Integral/Lebesgue/RestrictLimit` |
| Probability-law convergence and independence under weak limits | `Probability/ConvergenceInDistribution` | `Basic`, `Mapping`, and `Independence` cover convergence compatibility, continuous maps, and both directions of finite product/independence limits |
| Measurable counting-measure processes | `Probability/PointProcess` | `PointProcess` bundles a measurable map into Mathlib `Measure` with integer-valuedness and the chosen finite-on-family condition |
| Path-space geometry and generic tightness criteria | `Topology` and `Probability/Process/Path` | `CadlagPath`, Skorokhod oscillation and tightness modules |
| Finite step-corridor endpoint cores and inner-cell geometry | `Topology/Cadlag/Skorokhod/PathClass/StepCorridor/Partition` | `LowerCores` selects knot cores; `LowerGeometry` places finite real bounds in the common cells, without assumptions on a probability law |
| IID sequence laws, filtrations, and independence | `Probability/Sequence` | `Sequence/Block` owns measurable finite-block coordinates; `Sequence/IID/Basic` owns `iidSequenceLaw`, its finite-block product-law interface, and coordinate independence; stopping-time factorization remains in `Sequence/IID/StoppingTime` |
| General random-walk process laws and paths | `Probability/Process/RandomWalk` | path maps, kernels, Donsker and small-deviation interfaces |
| Stationary increment laws | `Probability/Process/StationaryIncrements` | `HasStationaryIncrements`; independent of independent-increment and path-regularity assumptions |
| Finite-dimensional laws from independent increments | `Probability/Process/IndepIncrements` | `FiniteDimensional` reconstructs position laws and identifies translated process laws from generic state-group hypotheses |
| Stable-law and stable-process semantics | `Probability/Distributions/Stable` and `Probability/Process/Stable` | stable distributions, clock increments, Lévy processes |
| Branching random-walk models and thesis-specific coupling | `Probability/BranchingRandomWalk` | offspring fields, spine, selected populations, restart coupling |
| BRW ancestral-path second moments and MRCA pair decomposition | `Probability/BranchingRandomWalk/Spine/Path` | `SecondMoment`; independent of corridor geometry and selection |
| Selection mechanisms, including random rules | `Probability/BranchingRandomWalk/Selection` | random and causal selection interfaces |
| Deterministic first-`N` selection, speed, and tail estimates | `Probability/BranchingRandomWalk/Selection/NSelection` | `NSelection`, selected-population endpoint/drawdown bounds, and speed proof |

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
- The local `PointProcess` bundles Mathlib measures with the measurability,
  integer-valuedness, and finite-on-family properties required of a random
  counting measure. Its branching-step adapter stays in the branching-random-
  walk layer.
- Countable independent product laws use `Measure.infinitePi` and the
  `iIndepFun` results in Mathlib. `iidSequenceLaw` names the homogeneous
  sequence specialization used throughout the library. Generic finite block
  coordinates and their measurability belong to `Probability/Sequence/Block`;
  the law of every such block and the probability of a measurable block event
  belong to `Probability/Sequence/IID/Basic`. These interfaces require only an
  IID sequence law and do not belong in random-walk entrance or stopping-time
  modules. Stopping-time-specific factorization stays in
  `Probability/Sequence/IID/Blocks/StoppingTime`.
- Transition mechanisms use Mathlib's `Kernel`/`MarkovKernel` interfaces.
  Killed kernels in the random-walk layer are restrictions of those kernels.
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

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
| Measure operations, integral limits, and measure properties | `MeasureTheory` | `Measure/Convolution/Power`, `Measure/DiracSum`, `Integral/Lebesgue/RestrictLimit` |
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
- Filtrations and stopping times use Mathlib's `Filtration` and stopping-time
  predicates. Process-specific adaptedness proofs are adapters from the
  process maps to those interfaces.
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
right abstraction. A public object should state the mathematical structure or
result with the weakest natural assumptions that its proof supports; a
single-use proof step stays private or under the owning module's `Lemmas/`
subtree. Before promoting a specialized result, look for a more general
interface in Mathlib, pinned dependencies, and the relevant literature, then
compare the actual assumptions and conclusion rather than matching names.
Generalize the local API when the broader statement has independent
mathematical meaning and can be proved without importing the application that
currently uses it. Record the searched sources, the closest general form, and
why it does or does not subsume the local result in this file or the directory
audit.

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

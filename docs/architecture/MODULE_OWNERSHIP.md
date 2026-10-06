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
| Deterministic asymptotic scales and limits | `Analysis/Asymptotics` | `Scale`, `InverseScale`, `BlockScale`, regular variation |
| Measure operations, integral limits, and measure properties | `MeasureTheory` | `Measure/Convolution/Power`, `Measure/DiracSum`, `Integral/Lebesgue/RestrictLimit` |
| Measurable counting-measure processes | `Probability/PointProcess` | `PointProcess` bundles a measurable map into Mathlib `Measure` with integer-valuedness and the chosen finite-on-family condition |
| Path-space geometry and generic tightness criteria | `Topology` and `Probability/Process/Path` | `CadlagPath`, Skorokhod oscillation and tightness modules |
| IID sequence laws, filtrations, and independence | `Probability/Sequence` | `iidSequenceLaw`, prefix filtrations, block independence |
| General random-walk process laws and paths | `Probability/Process/RandomWalk` | path maps, kernels, Donsker and small-deviation interfaces |
| Stable-law and stable-process semantics | `Probability/Distributions/Stable` and `Probability/Process/Stable` | stable distributions, clock increments, Lévy processes |
| Branching random-walk models and thesis-specific coupling | `Probability/BranchingRandomWalk` | offspring fields, spine, selected populations, restart coupling |

Directory names should follow the owning concept. A declaration is not moved
to a theorem-specific directory merely because that theorem currently uses it.
Conversely, a general-looking name does not justify a generic module if its
definition relies on stable, branching, or other model-specific hypotheses.

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
  sequence specialization used throughout the library.
- Transition mechanisms use Mathlib's `Kernel`/`MarkovKernel` interfaces.
  Killed kernels in the random-walk layer are restrictions of those kernels.
- Filtrations and stopping times use Mathlib's `Filtration` and stopping-time
  predicates. Process-specific adaptedness proofs are adapters from the
  process maps to those interfaces.
- Càdlàg paths and Skorokhod-space constructions reuse the path-space objects
  supplied by the project dependencies. Local criteria add the estimates and
  interfaces needed by this library's limit theorems.
- Finite affine grids are represented by `UniformGrid` with caller-supplied
  endpoints. Rational and dyadic grids provide arithmetic specializations.
  Mathlib's `Dyadic` and additive subgroups remain the right objects for
  unbounded dyadic coordinates and additive lattices, respectively.

When a local definition wraps one of these objects, its module should state
what extra semantics it supplies and keep the map to the underlying Mathlib
object explicit.

## Placement checks for new definitions

For each public object, answer these questions in review:

1. What is the mathematical data, independently of the theorem using it?
2. Does Mathlib already provide that data or a theorem with the same scope?
3. What is the weakest set of assumptions needed to define it?
4. Which lower layer owns those assumptions and operations?
5. Is this a genuine specialization/adapter, or an unnecessary parallel API?

Keep a model-specific assumption at the application boundary. For example,
the definition of a generic measurable path should not assume a stable law,
and a deterministic child step should not assume that a child exists or that
its slots are ordered.

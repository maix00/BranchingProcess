# Lean source architecture

The source tree follows the dependency direction. Deterministic data and maps
live under `Combinatorics`; probability laws, filtrations, independence, and
a.e. statements live under `Probability`.

## Main modules

```text
Combinatorics/
  UlamHarris/
    Tree/                       address trees and their graph views
    MarkedTree/                 trees carrying node marks
  Branching/
    Tree/Basic.lean             unmarked branching trees (the unit-mark case)
  BranchingWalk/
    Step/                       deterministic optional child slots
      Basic.lean
      Measurability.lean
      PointMeasure.lean         Dirac sum of present slots
      ExponentialWeight.lean    exp(-x) child weights
      Monotone.lean             ordered support
    Basic/                      step fields, survival, displacement, positions
    Tree/Genealogy.lean         forget displacements to an unmarked tree
    MarkedTree/
      Equivalence.lean          step-field/marked-tree conversions and round trips
      Order.lean                ordered slots versus sibling-monotone marks
      OfBranchingWalk.lean      conversions for root-indexed walks
    Selection/                  deterministic finite-population selection
    Cloud/                      generation clouds and their order
    Trajectory/                 space-time paths

MeasureTheory/
  Measure/
    DiracSum.lean               indexed optional Dirac sums
    FiniteOnFamily.lean
    AtomFiniteness.lean
    Domination.lean

Probability/
  PointProcess/Basic.lean       generic random counting-measure interface
  BranchingRandomWalk/
    Step/                       random counterparts of deterministic Step modules
      Basic.lean                measurable Ξ : Ω → deterministic Step
      PointMeasure.lean         measurability of deterministic observations
      PointMeasureLaw.lean      forward/backward pushforward equalities
      PointProcess.lean         adapter to generic PointProcess
      Order.lean                ordered/nonempty support under pushforward
      MultiRootLaw.lean         all labelled roots and addresses
      Law.lean                  product step-field laws
      OrderedSupport.lean
      Position/
    Genealogy/                  root-indexed laws, filtrations, explorations
    Population/                 candidate and selected population processes
    Timing/                     stopping times and causal measurability
    Spine/                      finite kernels and tilted-slot constructions
    Assumptions/                structural and moment hypotheses
```

## Interfaces and seams

`Combinatorics.Branching.Step ι X = ι → Option X` permits zero children. It is
the primitive deterministic reproduction object. Every observation used by the
probability layer, including support, child count, point measure, exponential
weight, and order, is first a deterministic function on this type.

`ProbabilityTheory.BranchingRandomWalk.Step Ω ι X` is the random interface. It
contains a measurable map
`Ω → Combinatorics.Branching.Step ι X`. The short name `Step` retains random
meaning through its namespace and file path. Its law is the pushforward of the
sample measure. No additional reproduction-variable wrapper is used.

A reproduction law is therefore introduced by a random variable `Ξ`, rather
than reconstructed by ranking the atoms of an abstract random measure. The
old measure-to-step and recursive atom-enumeration chain has been removed.
`Step.pointMeasure` only maps `Ξ` forward through the deterministic
Dirac-sum function. `Step.toPointProcess` is the one-way adapter to the generic
point-process interface.

`Combinatorics.Branching.Tree` is an alias for an unmarked Ulam-Harris tree and
contains no probability terminology. `Tree.toBranchingWalk` realizes it as a
unit-displacement walk, while `BranchingWalk.genealogicalTree` forgets marks.
These maps form the deterministic genealogy seam.

A marked tree retains displacement information. `MarkedTree/Equivalence.lean`
contains the conversion maps and round-trip theorems. The extra ordered
interface is isolated in `MarkedTree/Order.lean`: monotone child slots are
exactly sibling-monotone marks. This keeps order out of the base conversion.

For `m` initial particles, the probability layer uses a root index `Fin m`.
`finiteRootStepFieldLaw` supplies an independent step field for every labelled
root; `Step/MultiRootLaw.lean` proves each root/address has the law of `Ξ` and
transfers ordered and nonempty support simultaneously. Equal local addresses
under distinct roots remain distinct coordinates.

## Reused mathlib objects

Child point measures use mathlib `Measure`, `Measure.dirac`, and countable
measure sums through the local `Measure.iOptionDiracSum` adapter. The measurable
space on measures is mathlib's evaluation measurable space. The project keeps
a small generic `PointProcess` structure because mathlib does not provide the
specific counting-plus-local-finiteness package needed here.

The build target is the library declared by `lakefile.toml`; `lake build`
checks every module selected by its globs.

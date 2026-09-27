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
    Basic.lean                  unmarked `Process = BranchingWalk ... PUnit`
    Tree/Basic.lean             address-tree projection, a separate layer
  BranchingWalk/
    Step/                       deterministic optional child slots
      Basic.lean
      Map.lean                  functorial mark maps and forgetting marks
      Measurability.lean
      PointMeasure.lean         Dirac sum of present slots
      ExponentialWeight.lean    exp(-x) child weights
      Monotone.lean             ordered support
    Basic/                      step fields, survival, displacement, positions
      GenerationSize.lean       cardinality of `survivingParticlesAt`
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
      Field.lean                add the `TreeNode` index to random steps
      Map.lean                  measurable mark maps and unmarked step law
      PointMeasure.lean         measurability of deterministic observations
      PointMeasureLaw.lean      forward/backward pushforward equalities
      PointProcess.lean         adapter to generic PointProcess
      Order.lean                ordered/nonempty support under pushforward
      MultiRootLaw.lean         all labelled roots and addresses
      Law.lean                  product step-field laws
      OrderedSupport.lean
      Position/
    Genealogy/
      GaltonWatson.lean         single-root i.i.d. unmarked step-field law
      ...                       root-indexed laws, filtrations, explorations
    Population/                 candidate and selected population processes
    Timing/                     stopping times and causal measurability
    Spine/                      finite kernels and tilted-slot constructions
    Assumptions/                structural and moment hypotheses
```

## Abstraction order

The implementation proceeds through reusable interfaces in this order:

1. A deterministic optional-slot `Step ι X`, with no probability or algebra on `X`.
2. Functorial mark mapping. Mapping to `PUnit` forgets marks and preserves every survival event.
3. `Branching.Process`, the `PUnit`-marked special case of `BranchingWalk`.
4. `Branching.Tree`, the further projection onto surviving addresses.
5. A random displacement `StepDisplace Ω X = Ω → X`; a random `Step` is an
   `ι`-indexed family of these displacements together with a measurable Boolean
   presence coordinate for every slot. `Option X` appears only when the two
   coordinates are assembled into a deterministic step.
6. A random `StepField` adds the `TreeNode ι` index. Evaluating all coordinates
   at one sample produces a deterministic step field.
7. The single-root i.i.d. unmarked field law, named `galtonWatsonFieldLaw`; multiple roots use the existing root-indexed product construction.
8. Spatial point measures, ordered support, spine laws, and selected populations as structures or observations on the same random steps.

The indexed law `Step.indexedLaw` records a chosen slot enumeration. The
enumeration-independent reproduction law is `Step.branchingLaw`, the law of
the random point measure `Step.pointMeasure`.

Special cases instantiate these interfaces. They do not introduce parallel
step, tree, point-process, or population types.

## Interfaces and seams

`Combinatorics.Branching.Step ι X = ι → Option X` permits zero children. It is
the primitive deterministic reproduction object. Every observation used by the
probability layer, including support, child count, point measure, exponential
weight, and order, is first a deterministic function on this type.

`ProbabilityTheory.BranchingRandomWalk.Step Ω ι X` is the random interface.
Its primitive fields are `displace : ι → Ω → Option X` and a measurability
proof for each coordinate. The map
`Ω → Combinatorics.Branching.Step ι X` is assembled from those coordinates and
proved measurable. `ProbabilityTheory.BranchingRandomWalk.StepField Ω ι X`
then adds the address index `TreeNode ι`. No generic random-variable wrapper
or second reproduction object is introduced.

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

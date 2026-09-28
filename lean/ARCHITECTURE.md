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
    Walk/Basic.lean             one-branch (`PUnit` child-slot) walks
    Walk/Path/                  deterministic processes, histories, windows,
                                blocks, scaling, and horizontal/general corridors
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
      Processes/Parallel/       adapted concurrent unions and size bounds
    Timing/                     stopping times and causal measurability
    Spine/                      finite kernels and tilted-slot constructions
    Walk/
      Basic.lean                `PUnit`-slot random walks and survival
      Law.lean                  independent increment-path laws
      Path/Window.lean          measurability of deterministic path windows
      SmallDeviation/           random-walk tube probabilities
    Assumptions/                structural and moment hypotheses
```

## Abstraction order

The implementation proceeds through reusable interfaces in this order:

1. A deterministic optional-slot `Step ι Mark`, with no probability or algebra on `Mark`.
2. Functorial mark mapping. Mapping to `PUnit` forgets marks and preserves every survival event.
3. `Branching.Process`, the `PUnit`-marked special case of `BranchingWalk`.
4. `Branching.Walk`, the `PUnit` child-slot special case of `BranchingWalk`;
   `RandomWalk` is exactly the corresponding `BranchingRandomWalk PUnit`
   specialization. It may be killed. Permanent survival and realization by
   an everywhere-present increment path are separate properties.
5. `Branching.Tree`, the further projection onto surviving addresses.
6. A random edge-data coordinate `StepDisplace Ω Mark = Ω → Mark`; a random
   `Step` is an `ι`-indexed family of these coordinates together with a
   measurable Boolean presence coordinate for every slot. `Option X` appears only when the two
   coordinates are assembled into a deterministic step. `Step.full` is the
   generic constructor for models in which every indexed slot is present.
7. A random `StepField` adds the `TreeNode ι` index. Evaluating all coordinates
   at one sample produces a deterministic step field.
8. The single-root i.i.d. unmarked field law, named `galtonWatsonFieldLaw`; multiple roots use the existing root-indexed product construction.
9. Spatial point measures, ordered support, spine laws, and selected populations as structures or observations on the same random steps.

The indexed law `Step.indexedLaw` records a chosen slot enumeration. The
enumeration-independent reproduction law is `Step.branchingLaw`, the law of
the random point measure `Step.pointMeasure`.

Special cases instantiate these interfaces. They do not introduce parallel
step, tree, point-process, or population types.

Proof-only analytic lemmas are split by obligation under
`Probability/BranchingRandomWalk/Analytic/`: exceptional-event estimates and
the final speed-limit squeeze do not depend on the construction layers.

## Interfaces and seams

`Combinatorics.Branching.Step ι X = ι → Option X` permits zero children. It is
the primitive deterministic reproduction object. Every observation used by the
probability layer, including support, child count, point measure, exponential
weight, and order, is first a deterministic function on this type.

`ProbabilityTheory.BranchingRandomWalk.Step Ω ι Mark` is the random interface.
Its primitive fields are a Boolean `present` coordinate and a `displace`
(edge-data) coordinate `ι → Ω → Mark`, each with its measurability proof.
The map
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

A marked tree retains accumulated node positions. For a generalized walk, the
edge marks are first mapped by `d : Mark → Position` and accumulated; the
resulting `Position` values are the node marks. The `Mark = Position`, `d = id`
case is the paper-style displacement model. `MarkedTree/Equivalence.lean`
contains the conversion maps and round-trip theorems. The extra ordered
interface is isolated in `MarkedTree/Order.lean`: monotone child slots are
exactly sibling-monotone marks. This keeps order out of the base conversion.

The probability layer first uses an arbitrary root index `Root`.
`RootIndexed.stepFieldLaw` is mathlib's arbitrary-family probability product,
so the construction itself does not require `Root` to be countable. Every root
has a full independent step field, and injective reindexing preserves the
product law. `Root = ℕ` supplies one infinite pre-sampling for the asymptotic
number of initial particles; an injection `Fin m → Root` produces
`finiteRootStepFieldLaw` as a marginal. Countability enters only when combining
coordinatewise probability-one events into one event quantified over all
roots. Equal local addresses under distinct roots remain distinct coordinates.
Finite root sums do not define a second many-to-one formula:
`RootIndexed/FiniteExpectations.lean` transfers each measurable root
observable to its single-root law and then sums those equalities over a
`Finset Root`.

The fixed-subtree branching-property core is equally general in the child
slot type. `subtreeStepField`, the past/future/descendant measurable spaces,
their independence, and `fixed_subtreeStepFieldVector_law` use
`TreeNode α` and `Step α X`. The joint theorem accepts an arbitrary family
index `κ`; finiteness and countability enter only in later operations that
enumerate, sum, or partition over selected populations.

A random walk is single-root and has the singleton child-slot type `PUnit`.
Generation `n` therefore has at most the unique address `Walk.lineNode n`;
that address may be absent. A family of walks may be indexed by arbitrary
roots, but that indexing remains outside `RandomWalk`. The many-to-one layer
constructs `Spine.spineRandomWalk` from the tilted product law, proves its
increment-path realization and almost-sure permanent survival, and uses the
corresponding partial sums in the analytic formulas.

## Mark, position, and potential

The generalized deterministic walk has three separate roles:

- `Mark` is the data carried by an edge and need not have addition;
- `Position` is the additive space in which path increments are accumulated;
- `d : Mark → Position` converts one edge mark into one position increment.

A measurable real-valued `Potential` is a further observable used for ordering,
exponential weights, log-Laplace functionals, frontiers, or speeds. It should
not be confused with either the edge mark or the accumulated position. A
potential used only to order a cloud is an arbitrary measurable map
`Position → ℝ`. When pathwise scalar sums are needed, an
`AdditivePotential Position` supplies a measurable homomorphism
`φ : Position →+ ℝ`. The theorems `map_displaceWith` and
`potential_position` identify projection after accumulation with accumulating
the projected increments `φ ∘ d`. Thus marks may have no algebraic structure.
The one-dimensional model is recovered with
`Mark = Position = ℝ`, `d = id`, and `φ = id`.

## Reused mathlib objects

Child point measures use mathlib `Measure`, `Measure.dirac`, and countable
measure sums through the local `Measure.iOptionDiracSum` adapter. The measurable
space on measures is mathlib's evaluation measurable space. The project keeps
a small generic `PointProcess` structure because mathlib does not provide the
specific counting-plus-local-finiteness package needed here.

The build target is the library declared by `lakefile.toml`; `lake build`
checks every module selected by its globs.

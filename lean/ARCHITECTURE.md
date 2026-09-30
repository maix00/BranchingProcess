# Lean source architecture

The source tree follows the dependency direction. Deterministic data and maps
live under `Combinatorics`, general deterministic analysis under `Analysis`,
and probability laws, filtrations, independence, and a.e. statements under
`Probability`.

## Main modules

```text
Combinatorics/
  UlamHarris/
    Tree/                       address trees and their graph views; multi-root
                                variants live in the `RootIndexed` namespace
                                of the same files
      Singleton.lean            one-root specialization of `RootIndexed.Tree`
    MarkedTree/                 trees carrying node marks; multi-root variants
                                live in the `RootIndexed` namespace
      Singleton.lean            one-root specialization of `RootIndexed.MarkedTree`
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
      Relation.lean             relations between marks on sibling slots
      SiblingClosed.lean        initial-segment closure of surviving slots
      SiblingClosable.lean      injective relabeling into sibling-closed order
      Monotone.lean             mark monotonicity and `orderedSteps`
      Orderable.lean            relabeling arbitrary support into ordered form
    Basic/                      step fields, survival, displacement, positions
      Descendant.lean            descendant relations and generation slices
      Survival.lean              surviving particles and generation slices
      Ancestor.lean              reverse descendant relations and slices
      ParentSibling.lean         immediate parent and sibling relations
      SiblingClosed.lean         direct sibling-closed step-field predicate
      SiblingClosable.lean       injective relabeling of step fields
      GenerationSize.lean       cardinality of `survivingParticlesAt`
    Walk/Basic.lean             one-branch (`PUnit` child-slot) walks
    Walk/Path/                  deterministic processes, histories, windows,
                                blocks, scaling, and horizontal/general corridors
      Block/Partition/Basic.lean
                                block partial sums, telescoping, and block covers
      Block/Partition/Normalized.lean
                                normalized endpoint margins and corridor unions
      Corridor/Energy.lean      corridor width energy for rate-function proofs
      Corridor/Normalized.lean  normalized step-path corridor adapters
      Tree/Genealogy.lean         forget displacements to an unmarked tree;
                                  requires the separate sibling-closure property
    MarkedTree/
      Equivalence.lean          step-field/marked-tree conversions and round trips
      Order.lean                ordered slots versus sibling-monotone marks
      OfBranchingWalk.lean      conversions for root-indexed walks
    Selection/                  deterministic finite-population selection
      Coupling/Offspring/       root-preserving offspring candidate layers
        Address.lean             set-valued parent-slot addresses
        Finite.lean              finite candidate and cardinality adapters
        Cloud.lean               injective/rankwise cloud comparisons
      Coupling/Position.lean     spatial specialization of offspring coupling
      NSelection/Coupling/     multi-root spatial coupling induction
        Cloud.lean              finite population clouds and canonical rank maps
        Offspring.lean          parent-to-child lower-tail propagation
        Step.lean               first-N one-generation injection and recursion
    Cloud/                      generation clouds and their order
    Trajectory/                 space-time paths

MeasureTheory/
  Measure/
    DiracSum.lean               indexed optional Dirac sums
    FiniteOnFamily.lean
    AtomFiniteness.lean
    Domination.lean

Analysis/
  Asymptotics/
    Tolerance.lean             deterministic `ENNReal.ofReal` error selection
  SpecificLimits/              deterministic limit calculations
  SpecialFunctions/            deterministic special-function estimates

Probability/
  Asymptotics/                 deterministic scales, rounding, and inverse scales
  Distributions/
    Gaussian/Interval.lean     nondegenerate Gaussian interval positivity
    Gaussian/FiniteProduct.lean finite products and interval inclusions
    Moments/Real.lean           centered real laws and second-moment transport
    Moments/Signs.lean          positive and negative half-line mass facts
    Stable/                     stable laws and Gaussian specialization
  Process/
    IndepIncrements.lean        independent-increment process interfaces
    IndepIncrements/
      Disjoint.lean              independence of separated increment families
      DisjointPaths.lean         independence of complete paths on adjacent intervals
      FiniteGrid.lean            canonical enumeration of finite time grids
      BlockVectors.lean          measurable partial sums on disjoint blocks
      FiniteBlockPaths.lean      finite observation paths assembled from blocks
      FiniteDimensional.lean     generic finite-grid and process-law theorems
    Path/
      Continuous.lean            continuous path-valued process interface
      UnitInterval.lean          unit-interval restriction and identity clock
      Skorokhod.lean             generic càdlàg coordinate process and
                                 continuous-path embedding
      Skorokhod/                  rational-coordinate process restrictions
        RationalTime.lean        horizon restriction on rational unit times
        Corridor/                generic rational-coordinate corridor partitions
          UniformBlocks.lean     block times/clocks, paths, measurability, and tube inclusions
          UniformBlocks/Prefix.lean
                                 deterministic stopped prefixes and prefix tube sets
          UniformBlocks/Events.lean
                                 measurable block/prefix events and prefix identities
          UniformBlocks/Probability.lean
                                 generic measure bounds for independent block paths
          UniformBlocks/Gluing.lean
                                 spatial corridor sets, endpoint bins, and block gluing
    Path/Tightness/             generic continuous-path oscillation and tightness criteria
      Oscillation.lean          measure-level oscillation diagonalization
      Criteria.lean             Arzelà--Ascoli tightness interfaces
    Stable/
      Basic.lean                stable clock-increment specification
      Process.lean              càdlàg stable clock processes
      Levy.lean                 identity-clock stable Lévy specialization
      FiniteDimensional.lean    finite-grid position laws and scaling
      PathLaw.lean              stable laws on càdlàg path space; uses the
                                generic coordinate process from `Path/Skorokhod`
      EscapeRate.lean           finite-horizon stable range-tube interface
      Brownian.lean             Brownian exponent-two specialization
      SmallDeviation/
        RationalTube.lean       rational-time tube measurability and stable scaling
        Blocks.lean             stable Lévy translated-block laws and adapter
        Blocks/Independence.lean  adjacent-block path independence
        Blocks/Factorization.lean stopped-prefix independence and product steps
        Blocks/Upper.lean       stable uniform-block upper bounds
        Blocks/Lower/Binning.lean endpoint-bin lower block factorization
        Blocks/Lower/Concatenation.lean
                                 corridor lower recurrence and finite-block iteration
        Blocks/Lower/Return.lean core-return recurrence and finite-block iteration
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
      Processes/Causal/         pathwise bounds, spine first moments, and capacity bridges
        RelativePosition/       causal window constructions
          Basic.lean             general ancestral relative-position populations
          Finite.lean             directional finite-slice adapters
          Real.lean               real negative-exponential restart construction
        PathBound.lean          pathwise population-to-path domination
        FirstMoment.lean        root-indexed one-dimensional first-moment bounds
        CapacitySpine.lean      capacity estimates from restarted-window moments
    Selection/                  random and domain-flow selection interfaces
      Random.lean                arbitrary-set random selection
      Causal.lean                arbitrary-set domain-flow selection
      Finite.lean                finite-candidate selection and kernels
      FiniteCausal.lean          finite-candidate domain-flow selection
    Coupling/Field/Ranked/       recursive rank-matching layers
      Basic.lean                deterministic left/right copies and stage update
      Measurability/             generation-domain-flow measurability
        Past.lean               recursive past measurability
        Field.lean              matched-field filtration measurability
        Observables.lean        selected populations and positions
      Law.lean                  finite-stage product-law preservation
    Coupling/Rank/               rank matching primitives
      Preimage.lean              finite-support rank inverse and optional lookup
      Choice.lean                one-generation equal-rank source choice
      Block.lean                 fresh block-coordinate map and gluing identities
      Field.lean                 rank-installed StepField and its measurability
      Adaptive.lean              predictable rank-splice product law
      Law.lean                   fixed rank-installation product law
    Timing/                     stopping times and causal measurability
    Spine/                      finite kernels, generation decompositions, and tilted-slot constructions
      GenerationBranching/      address decomposition, joint measurability, and endpoint recursion
      EndpointRealization/      independent-increment and branching-field endpoint recursions
    Walk/
      Basic.lean                `PUnit`-slot random walks and survival
      Law.lean                  independent increment-path laws
      Kernel/Killed/Blocking.lean killed-kernel blocking for horizontal tubes
      Path/Window.lean          measurability of deterministic path windows
      Path/Restart/Basic.lean   restarted-window laws and translation invariance
      Path/Restart/Corridor.lean IID factorization for horizontal corridors
      Path/Corridor/             random-walk tube events and probabilities
      SmallDeviation/           Mogulskii small-deviation estimates
        Mogulskii/Spectral/     killed-interval sine modes and estimates
          Modes.lean             Dirichlet modes, eigenvectors, and sine basis
          Basis.lean             orthogonal coordinates and coefficient bounds
          Expansion.lean         finite matrix-power spectral expansion
          UpperBound.lean        geometric row-mass upper bound
          Scaling/               variable-width spectral asymptotics
            Power.lean             principal eigenvalue and geometric corrections
            Upper.lean              diffusive-scale upper bounds
            Lower.lean              diffusive-scale lower bounds
            Interior.lean           uniformly interior starting sites
            Endpoint.lean           endpoint sine-prefactor conditions
  Assumptions/                structural, moment, and cross-weight hypotheses

Topology/
  Cadlag/Skorokhod/Oscillation/
    Dense.lean                dense-time range bounds for càdlàg paths
```

The stable distribution layer is kept independent of small-deviation scales:
`Probability/Distributions/Stable/Gaussian.lean` contains only the Gaussian
stability theorem, while the truncated-variance limit for `L*` lives in
`Walk/SmallDeviation/Mogulskii/Gaussian/DonskerSpecialization.lean`.

`Probability/Process/Stable/SmallDeviation/RationalTube.lean` is the
small-deviation adapter for stable processes. It proves measurability of the
rational-coordinate target set and the exact time-space reparameterization
that turns a small-width tube into a long-horizon tube. The application-level
bridge to the `CadlagPath` tube law, the escape-rate limit, and the final
stable Mogulskii estimate remain separate obligations in `EscapeRate.lean`
and the Mogulskii modules.

The canonical rational-time embedding and arbitrary-process horizon restriction
are lower-level path interfaces in
`Probability/Process/Path/Skorokhod/RationalTime.lean`; the stable file imports
them instead of defining them locally.

The unit-interval identity clock and the canonical càdlàg coordinate process
are also path-space primitives.  They live in
`Probability/Process/Path/UnitInterval.lean` and
`Probability/Process/Path/Skorokhod.lean`, respectively, so stable modules only
add the stable increment and escape-rate specifications that use them.

The uniform block partition is deliberately lower-level:
`Probability/Process/Path/Skorokhod/Corridor/UniformBlocks.lean` contains only
deterministic block times and clocks, path restrictions, their measurability,
the deterministic tube inclusion, and the generic independent-family product
formula.  Its `UniformBlocks/Prefix.lean` sibling adds the deterministic
stopped prefix path and prefix tube set.  The stable adapter in
`Probability/Process/Stable/SmallDeviation/Blocks.lean` adds the translated
stable Lévy path law and its common block law; it no longer owns the generic
time, path, or measure constructions.

The killed-interval spectral layer follows the same one-direction rule.  The
mode and basis interfaces are imported by the finite expansion, and only the
geometric row-mass consumer imports `UpperBound.lean`; there is no aggregate
`Spectrum.lean` re-export file.

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

The source tree does not maintain umbrella modules that only re-export an
entire directory. Consumers import the concrete layer they use; small nested
entries such as `Population/Processes/Concurrent.lean` remain when they name a
coherent sublayer.

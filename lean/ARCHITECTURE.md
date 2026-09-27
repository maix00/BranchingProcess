# Lean source layout

The source tree follows the mathematical dependency direction. Files should
stay small enough to have one principal definition or proof layer.

```text
Combinatorics/                mathlib candidates outside the thesis
  SimpleGraph/Acyclic/Height.lean  acyclicity from a height function,
                              at the mathlib path `Mathlib.Combinatorics.SimpleGraph`
MeasureTheory/                measure-theoretic infrastructure
  UlamHarris/                 deterministic address combinatorics
    Basic.lean                TreeNode, 𝕍, Mark
    Tree/Basic.lean           the Tree structure and its measurable space
    Tree/Graph/Basic.lean     the parent relation and the Digraph, Quiver, SimpleGraph projections
    Tree/Graph/Arborescence.lean  the parent-child quiver as a Quiver.Arborescence
    Tree/Graph/Connected.lean the underlying graph is connected
    Tree/Graph/Acyclic.lean   the underlying graph is acyclic
    Tree/Graph/IsTree.lean    the underlying graph is a SimpleGraph.IsTree
    Tree/RootIndexed/Graph/Basic.lean      the forest of a root-indexed tree
    Tree/RootIndexed/Graph/Acyclic.lean    the forest is acyclic
    Tree/RootIndexed/Graph/Connected.lean  the forest is connected for one root
    Tree/RootIndexed/Graph/IsTree.lean     the forest is a tree for one root
    Tree/RootIndexed/Graph/Singleton.lean  the Tree graph as the one-root case
    MarkedTree/Basic.lean     the MarkedTree structure, its extensionality, its measurable space
    MarkedTree/SiblingOrder.lean  sibling monotonicity of the marks
    MarkedTree/Forget.lean    forget the marks of a marked tree, and its measurability
    MarkedTree/RootIndexed/Forget.lean  the root-indexed forgetful map to `UlamHarris.RootIndexed.Tree`
    Split.lean                the declared-split predicate
  BranchingWalk/              branching-step combinatorics
    Step/Basic.lean           `Step ι X = ι → Option X`, σ-algebra, value readings, `NatStep`, presence, support
    Step/Relation.lean        relation-parameterized order condition on present slots
    Step/Monotone.lean        increasing/decreasing mark order, sibling closure, OrderedStep, ordered step subsets
    Step/Monotone.lean  measurability of the ordered slot conditions
    Step/Field.lean           primitive step fields
    Basic/Definitions.lean   presence-closed and ordered step fields, and their projections
    Step/Measurability.lean   support measurability and truncation rules
    Step/PointMeasure.lean    Dirac sums of a step and their evaluation
    Basic/Displace.lean       total path displacement and its sum bridges
    Basic/Displace.lean     the `Option` displacement and its sum bridges
    Basic/Position.lean     initial-position-shifted node positions
    Basic/Displace.lean        the realized-child predicate of one slot
    Tree/Realization.lean     which addresses a field realizes
    Tree/Realized.lean        realized tree and marked tree of a presence-closed field
    Tree/Correspondence/Basic.lean  reading a step field off a marked tree
    Tree/Correspondence/Equiv.lean  the exact field-to-marked-tree correspondence
    Tree/Correspondence/RootIndexed.lean  one field per root and the root-indexed correspondence
    Cloud/Basic.lean          time-indexed clouds, membership, step-field generation, order-dual transport
    Cloud/Measurability.lean  the coordinate σ-algebra on clouds
    Cloud/SliceMeasure.lean   Dirac sum of each cloud time slice
    Cloud/Order/Slice.lean    domination order on one time slice and its order-dual instance
    Cloud/Order/Basic.lean    domination order on clouds, slice by slice
    Cloud/Order/Slice.lean    the slice order on the Dirac sums and its rankwise form
    Cloud/Order/Basic.lean    the slice order at every time
    Cloud/Frontier/Basic.lean least and greatest points of each cloud time slice
    Trajectory/Basic.lean     space-time vertex and edge images
    Trajectory/Step.lean      root-indexed trajectories and the single-root case
    Trajectory/Measurability.lean  trajectory σ-algebra and cloud projection
    Selection/
      Basic.lean              selection mechanisms on finite candidate sets
      Contain.lean            SelectContain: the containment order on BranchingWalk
      Mechanism.lean          SelectionMechanism: a containment-preserving endomorphism
      NSelection/
        Basic.lean            NBranchingWalk and NSelection: capacity-N mechanisms
      Card.lean               the leftmost rule: rank, cardinal bound, idempotence
      Mirror.lean             the rightmost rule as the order dual of the leftmost one
      Walk.lean               deterministic `N`-branching walks: step, population, cloud
      Cloud.lean              the walk cloud: slice cardinality and order-dual transport
      Frontier.lean           frontier sets and points of a generation, order duality
      Speed.lean              asymptotic speed of a frontier path
  Measure/
    FiniteOnFamily.lean       the single finiteness condition and its families
    DiracSum.lean             Dirac sums of indexed and option-valued families
    AtomFiniteness.lean       finite sublevel sets of a finite ENNReal weight
    Domination.lean           a.e. finiteness from an integrable dominator
Probability/                  anything with a law, a filtration, or an a.e. claim
  PointProcess/
    Basic.lean                the abstract point process on `E`
  BranchingRandomWalk/        the branching random walk, one domain
    Tree/Filtration.lean      generation spaces and the generation filtration
    Step/
      Law.lean                product laws, marginals, and independence
      DisplacementLaw.lean    injectively reindexed displacement independence
      OrderedSupport.lean     ordered support transfers to every address
      Position/Measurability.lean  realized nodes and displacements under the filtration
    PointProcess/
      Basic.lean              point measure induced by a branching-step field
      PointMeasure.lean       child Dirac sums built from mathlib measures
      Representation/         measurable monotone slot enumerations
        MonotoneEnumeration.lean  generic mark type, relation, and slot law
        RealLineEnumeration.lean  the real-line laws of the slot enumeration
        RankedAtom.lean           canonical ranked atom of a counting measure
        RankedAtomLocation.lean   rational rank bounds and their limits
        RankedOrder.lean          order and nonemptiness of ranked slots
        RankedReconstruction.lean Dirac-sum reconstruction of the input measure
        FromMeasure.lean      sample-space wrapper around the ranked construction
      Enumeration/            first/next atom and coverage
        FirstAtom/Selector.lean       leftmost realized slot and its measurability
        FirstAtom/Weight.lean         finite exponential weight of the children
        FirstAtom/Displacement.lean   selected displacement and ordered support
        NextAtom.lean         recursive raw-slot enumeration
        Recursive.lean        the recursion and its measurability
        Coverage.lean         coverage of the raw slots
      Law/MultiRootRepresentation.lean  the multi-root law of the slot process
    Genealogy/
      RootIndexed/
        Field.lean            root-indexed step fields and their reindexings
        Law.lean              finite-root product laws and marginals
        Positions.lean        root-indexed marks, positions, and realization
        Filtration.lean       the multi-root step filtration
        Measurability.lean    realized nodes and positions, root by root
      Exploration/
        Abstract/             abstract branching-property scaffolding
        RootIndexed/          root-indexed scaffolding
        Selected/             selected subtrees, descendant populations
      Lineage/
        Lineages.lean         pre-sampled reserve lineages and their split times
        MultiRoot.lean        the same for every labelled initial root
    Population/
      Candidates/             candidate generation, ordering, leftmost selection
      Processes/              selected, backbone-truncated, fully truncated processes
      Growth/                 deterministic population-size estimates
    Timing/                   stopping times, observability, split times
    Spine/                    many-to-one ingredients
    Assumptions/              moment and structural hypotheses on the law
    Analytic.lean             deterministic closing estimates
```

## Tree and step objects

The words "tree", "marked tree", and "step field" name three different
objects and must not be conflated.

- `TreeNode α` is the abstract address type `List α`. It is a word type over
  the child labels `α` and is not tied to `ℕ`.
- `𝕍 := TreeNode ℕ` is the Ulam--Harris node set `⋃ₙ ℕⁿ` of the paper. Code
  that works with natural-number child labels writes `𝕍`, matching the
  notation of the thesis.
- `Tree α` is a deterministic rooted tree of `TreeNode α`
  addresses: a carrier together with the root, parent, and ordered-sibling
  axioms. `Tree ℕ` is the `ℕ`-indexed case. A bare `Set (List α)` is
  only its carrier, never the tree itself. The namespace `UlamHarris`
  disambiguates the name from mathlib's deprecated `Tree` alias. `Tree` lives
  in `UlamHarris/Tree/Basic.lean`, which also carries the measurable space on
  trees: the one induced by the carrier, generated by `{T | u ∈ T.carrier}`
  for all addresses `u`. Thus a random tree is measurable exactly when
  membership of every address is measurable.
- `Tree.parentRel a b` is the address-level relation "`b` is a child of `a`",
  defined once in `UlamHarris/Tree/Basic.lean` and reused by every graph
  projection: a node has at most one parent (`Tree.parentRel_left_unique`) and
  a child address is strictly longer (`Tree.parentRel_length_lt`). It is a
  different relation from `BranchingWalk.parentRel`, which orders the present
  slots of a single branching step.
- `UlamHarris/Tree/Graph/` reads a tree as a mathlib graph on its realized
  carrier `↥T.carrier`: `childDigraph` is the Prop-valued `Digraph` of
  parent-child steps, `childQuiver` is the same relation as a quiver whose
  arrows are the child labels (`childQuiver_isThin`,
  `childQuiver_arborescence`, a `Quiver.Arborescence`), and `childGraph` is the
  undirected symmetrization `SimpleGraph.fromRel`. All of them live on an
  arbitrary label type `α`. `Graph/Connected.lean` proves that the root reaches
  every realized node, `Graph/Acyclic.lean` that the graph has no cycles, using
  the address length as a height, and `Graph/IsTree.lean` concludes
  `childGraph_isTree : (childGraph T).IsTree`. This is the check that the
  address space `Tree α` really projects to a mathlib tree.
- `Combinatorics/SimpleGraph/Acyclic/Height.lean` isolates the height argument:
  a simple graph in which every vertex has at most one neighbour of height not
  exceeding its own is acyclic (`SimpleGraph.isAcyclic_of_height`). Both the
  tree and the forest take the address length as height, so the cycle argument
  is proved once. The statement is independent of the thesis, so it lives at
  the mathlib path: the package root mirrors the mathlib root without the
  `Mathlib.` prefix, which belongs to the dependency, and the file is a
  candidate for `Mathlib.Combinatorics.SimpleGraph.Acyclic`. It is listed in
  `lakefile.toml` so that `lake build ThesisSpeed` compiles it.
- `UlamHarris/Tree/RootIndexed/Graph/` is the forest projection. A root-indexed
  tree is a family of trees, one per initial ancestor, so `forestGraph T` is the
  disjoint union of the child graphs of the family, with vertex set the realized
  pairs `(r, u)`. It is acyclic (`forestGraph_isAcyclic`) however many trees the
  family has, and it is connected (`forestGraph_connected`) and a mathlib tree
  (`forestGraph_isTree`) exactly in the one-root case `[Unique Root]`. A walk
  stays inside one tree of the family (`forestGraph_walk_root_eq`), so with
  several initial ancestors the components are separate and the object is a
  forest, not a tree. `Graph/Singleton.lean` records the specialization:
  `uniqueForestGraphIso` is the graph isomorphism between a one-root forest and
  `Tree.childGraph (T default)`, and
  `childGraph_isAcyclic_iff_forestGraph`, `childGraph_connected_iff_forestGraph`,
  and `childGraph_isTree_iff_forestGraph` say that the `Tree` versions are
  exactly that one-root case. The general object is the forest; the single
  `Tree` stays the base case of the dependency order of `Basic.lean`.
- `MarkedTree α X` pairs a `Tree α` with a mark on each realized
  node. It lives in `UlamHarris/MarkedTree/Basic.lean`, whose measurable space
  is induced by `M ↦ (M.tree, M.mark?)`, so both the realized carrier and the
  `Option`-valued mark reading are measurable coordinates.
- `Mark α M` is the mark function `TreeNode α → M` of the paper: it carries a
  mark at every address, realized or not, and the generation filtration is
  defined on it. `Mark ℕ M` is the mark function on `𝕍`. The name `Mark`
  denotes this object, not a single mark; a single mark is a term of the value
  type `M`.
- A `MarkedTree` carries marks only on its realized nodes, that is, on part of
  the address space. Mathlib represents a function whose domain is only part
  of a type as a partial function `α →. β = α → Part β`
  (`Mathlib/Data/PFun.lean`), so the marks of a `MarkedTree` are exposed as
  `MarkedTree.partialMark : TreeNode α →. M`, whose domain is the realized
  tree. The `Option`-valued accessor `MarkedTree.mark?` follows mathlib's
  convention of a `?` suffix for partial accessors such as `List.get?`. No
  `?`-suffixed *type* is introduced: `?` names functions returning `Option`,
  not types.
- `BranchingWalk α X` is the primitive field `TreeNode α → Step α X`
  of branching steps, with address labels and child labels in the same type
  `α`. A slot may be absent, so a field is not itself a tree and is not wrapped
  in a tree-named type. Write `value ξ i` for the raw optional mark `ξ i` and
  `value' ξ i` for its zero-defaulted reading. The defaulted reading needs a
  `Zero X` instance and is therefore a derived function, not part of `Step`.
  The derived objects are the displacement `displace`, which carries the address
  it starts from (`displace ω v p` is the displacement from the address `v` along
  the remaining path `p`), the partial mark `displace?` (returning `none` when
  some slot on the path is absent), and the marked tree `markedTree`, whose tree
  is the realized-address set of a presence-closed field
  (`Combinatorics/BranchingWalk/Tree/Correspondence/Basic.lean`).
  The path recursion carries the current address as an explicit carry
  (`displace ω v p`, `presentAlong`), so the realized tree and the marks
  never reconstruct an address from a list index; the partial mark follows the
  same skeleton in `Option` (`displace? ω v p`), so it is a computable
  definition that needs neither `classical` nor a decision procedure for
  realization. The root displacement and the root partial mark are the
  instances at the empty address, `displace ω [] u` and `displace? ω [] u`; a
  definition that only fixes the starting address is deliberately not kept.
  The paper's sum over the prefixes of the address is kept as a bridge, in a
  `Finset.range` form and a `Fin.length` form, and for both marks:
  `displace_eq_sum`, `displace_eq_sum_fin`,
  `displace?_eq_some_sum_iff` and
  `displace?_eq_some_sum_fin_iff`. Root-indexed displacement is not defined
  again either: `ProbabilityTheory.BranchingRandomWalk.RootIndexed` reads the
  displacement at one fixed root
  (`RootIndexed.displace step i u = Combinatorics.Branching.displace (step i) [] u`).

`Step` (full name `MeasureTheory.BranchingWalk.Step`) is the primitive object
and displacements are derived quantities, so the derived quantities are named
`displace` and `displace?` rather than being called paths, trees, or
positions.

## The connection layer between step fields and marked trees

Several objects present the same random walk, and the files below record how
they are related. The dependency direction is

`BranchingWalk` → `RootIndexed.BranchingWalk` → `OrderedStep` → marked trees,

with `MarkedTree α X` on the single-tree side and
`UlamHarris.RootIndexed.MarkedTree Root α X = Root → MarkedTree α X` on the multi-root
side.

- `BranchingWalk.RootIndexed.BranchingWalk α X` is the subtype of step fields
  whose every step lists its present slots from the left (`presenceParent`).
  This is exactly the condition under which the realized addresses form a
  `Tree`, so `realizedTree` and `markedTree` are defined on this subtype
  (`BranchingWalk/Basic/Definitions.lean`,
  `BranchingWalk/Tree/Realized.lean`). `toBranchingWalk` forgets the condition.
- `BranchingWalk.OrderedStep α X` adds the thesis's mark order
  (`parentOrdered`): the present marks increase along the slot order.
  `toRootIndexed.BranchingWalk` forgets only the mark order and `toBranchingWalk`
  forgets both; the two projections commute. These are the field-level
  projections: a result stated on the subtype needs the corresponding
  hypothesis on a primitive field. The root-indexed versions
  `RootIndexedBranchingWalk`, `RootIndexedRootIndexed.BranchingWalk`, and
  `RootIndexedOrderedStep` are in
  `BranchingWalk/Tree/Correspondence/RootIndexed.lean`; for `α = ℕ` the
  `RootIndexedBranchingWalk` there is the field of the probability layer.
- `BranchingWalk.stepOfMarkedTree` reads a step field off a marked tree: the
  slot `i` at the address `u` is present exactly when `u ++ [i]` is a realized
  node, and its value is the relative displacement
  `mark (u ++ [i]) - mark u`. This is the inverse reading of `markedTree`,
  which marks every realized node by its displacement
  (`BranchingWalk/Tree/Correspondence/Basic.lean`).
- The exact statement is
  `realizedOrderedStepEquivMarkedTree : RealizedOrderedStep α X ≃
  {M : MarkedTree α X // IsBranchingMarkedTree M}`, over an additive group. A
  tree records nothing below its realized nodes, so the field side is
  normalized by `RealizedSupport` (every slot of an unrealized address is
  absent); a marked tree is in the image exactly when its root mark vanishes
  and its sibling marks increase (`MarkedTree.siblingMonotone`), which is the
  thesis's convention of listing the children of a node by increasing
  displacement. `rootIndexedRealizedOrderedStepEquivMarkedTree` is the
  same statement for one field and one marked tree per initial ancestor
  (`BranchingWalk/Tree/Correspondence/Equiv.lean`,
  `.../Correspondence/RootIndexed.lean`).
- `MarkedTree.forgetMark` and `UlamHarris.RootIndexed.MarkedTree.forgetMark` go the other
  way, from marks to trees: forgetting the marks of a root-indexed family is
  the map `UlamHarris.RootIndexed.MarkedTree Root α X → UlamHarris.RootIndexed.Tree Root α` given by
  the tree of every initial ancestor. Both are measurable, and the root-indexed
  one commutes with reindexing the roots (`forgetMark_reindex`) and with the
  identification of the one-root case (`forgetMark_equivOfUnique`).

## Point processes

- `IsCountingMeasure` is defined for a measure on any measurable space `E`.
  It is the integer-valued condition: every measurable set has measure in
  `ℕ ∪ {∞}`.
- `IsFiniteOnFamily ν 𝒜` in `MeasureTheory/Measure/FiniteOnFamily.lean` is the single
  finiteness condition: `ν` is finite on every member of a family `𝒜` of
  sets. It mentions no order, topology, or real line.
- `compactFamily` instantiates it as Mathlib's `IsFiniteMeasureOnCompacts`
  (the standard point-process axiom); `leftRayFamily` and `rightRayFamily`
  instantiate it as finiteness on half-lines, spelled in Mathlib's canonical
  form `Set.range Set.Iic` / `Set.range Set.Ici` so that `isPiSystem_Iic`,
  `isPiSystem_Ici`, and `borel_eq_generateFrom_Iic` apply directly. Left and
  right are the same definition applied to mirrored families (the right rays
  are the left rays of `OrderDual`), so no theorem is left-only; what is
  asymmetric is only the direction of the enumeration chosen later.
- `PointProcess Ω E 𝒜` in `Probability/PointProcess/Basic.lean` is the abstract
  point process: a measurable map into the space of counting measures on `E`
  that are finite on `𝒜`. The measurable space on `Measure E` is Mathlib's
  evaluation sigma-algebra from the Giry monad. The family is a parameter, so
  the thesis condition is not hardcoded. It mirrors Mathlib's
  `Probability/Kernel/`: the object itself is a random measure, so it lives
  under `Probability/` in the `ProbabilityTheory` namespace, while its
  branching-random-walk realization stays in the branching random walk.
- `Measure.iDiracSum` in `MeasureTheory/Measure/DiracSum.lean` is the Dirac sum
  `∑ i, δ_{f i}` of an indexed family, and `Measure.iOptionDiracSum` is its
  option-valued form. Mathlib already defines the counting measure as
  `Measure.count = Measure.sum Measure.dirac` and proves
  `Measure.sum_smul_dirac`, `Measure.map_eq_sum`, and
  `Measure.count_apply : count s = s.encard`, so this file adds only the
  packaged form and its evaluation lemmas.
- `Combinatorics/BranchingWalk/Step/PointMeasure.lean` holds the `Step`
  instance: `stepPointMeasure ξ = Measure.iOptionDiracSum ξ` is the Dirac sum
  over the present slots, with the per-slot atoms and the evaluation lemmas.
  It is deterministic; no probability measure is involved.
- `Combinatorics/BranchingWalk/Cloud/SliceMeasure.lean` holds the cloud
  instance: `Cloud.iDiracSum C : Time → Measure X` is the counting measure
  `Measure.count.restrict (C.points t)` of each time slice.
- `StepPointProcess Ω ι X 𝒜` refines the abstract point process by a measurable
  branching step whose Dirac sum is the samplewise measure. The thesis
  specialization is `RealStepPointProcess Ω := StepPointProcess Ω ℕ ℝ
  (leftRayFamily ℝ)`; swapping in `rightRayFamily ℝ` gives the mirror object
  without touching any other definition.
- `Combinatorics/BranchingWalk/Cloud/Order/DiracSum.lean` transplants the
  domination order to those Dirac sums: `SliceDominatesMeasure μ ν` is
  `∀ a, μ (Iic a) ≤ ν (Iic a)` and `Cloud.DominatesMeasure` is its
  time-slicewise lift. `sliceDominates_iff_count_restrict` and
  `dominates_iff_iDiracSum` show that the set-level order and the measure-level
  order agree whenever the slices and half-lines are measurable; the set-level
  `encard` form stays primitive because it needs no measurable structure.
- `MonotoneEnumeration ν rel` is the measurable optional-slot representation
  of a measure-valued map `ν : Ω → Measure X`. Both the mark type `X` and the
  ordering relation `rel` are parameters, so the structure is not tied to `ℝ`
  and increasing and decreasing enumerations are instances of one definition;
  the thesis instance is `MonotoneEnumeration (X := ℝ) Ξ (· ≤ ·)`.
- `IsLeftLocallyFinite.isFiniteMeasureOnCompacts` shows the paper's left-ray
  condition implies the compact-finiteness axiom on `ℝ`.
- `MeasureTheory/Measure/Domination.lean` states the abstract form of the paper's
  derivation: a random measure dominated on a family by an integrable
  functional is a.e. finite on that family. The countable version collects the
  statements into one good event.

## Slot, representation, and enumeration

These names are three layers of the same realization of a point process.

- `Combinatorics/BranchingWalk/Step/` is the target vocabulary, and it is
  deterministic: it needs no probability measure. `Step ℕ ℝ = ℕ →
  Option ℝ` writes slot `i` as `some x` when the `i`th child is present at
  displacement `x`, and as `none` otherwise. `Step/Measurability.lean` names presence,
  displacement, nonemptiness, and truncation; `Step/Monotone.lean` names
  the ordered subset `orderedSteps` together with the explicit-relation form
  `orderedStepsOf` and the decreasing mirror `antitoneSteps`, and
  `Step/Monotone.lean` proves both instances measurable;
  `Basic/Displace.lean` records the
  deterministic position vocabulary and `Tree/Realization.lean` the
  realization predicate; their measurability under
  the generation filtration is not deterministic and lives in
  `Probability/BranchingRandomWalk/Step/Position/Measurability.lean`; the generic Dirac
  sum of a step is deterministic and lives in
  `Combinatorics/BranchingWalk/Step/PointMeasure.lean`, while its real-line
  slot-coordinate measurability lives in
  `Probability/BranchingRandomWalk/PointProcess/PointMeasure.lean`.
- `Probability/BranchingRandomWalk/PointProcess/Representation/` is the bridge
  from an abstract measure-valued input to that vocabulary.
  `MonotoneEnumeration ν rel` is the generic structure, with mark type `X` and
  ordering relation `rel` as parameters;
  `RealLineEnumeration.lean` contains its real-line laws;
  `RankedAtom.lean` builds the canonical ranked atom of a counting measure,
  `RankedAtomLocation.lean` locates each rank, `RankedOrder.lean` records its
  order and nonemptiness, `RankedReconstruction.lean` reconstructs the input
  measure, and `FromMeasure.lean` applies it samplewise.
- `Probability/BranchingRandomWalk/PointProcess/Enumeration/` holds the
  first/next-atom algorithms for a raw mark that is already slot-indexed but
  not yet ordered by position.
  `FirstAtom/Selector.lean` selects the leftmost realized slot and resolves
  position ties by the raw slot number, `FirstAtom/Weight.lean` turns a finite
  first moment of the exponential child weight into a genuine leftmost child
  almost surely, and `FirstAtom/Displacement.lean` records the measurability
  and minimality of the selected displacement.

## Namespaces and directories

There is no project namespace. Every declaration lives in the namespace of the
mathematical area it extends, following mathlib's convention that no `Mathlib`
namespace exists and that a file path matches its namespace.

| Directory | Namespace |
| --- | --- |
| `MeasureTheory/UlamHarris/` | `MeasureTheory.UlamHarris` |
| `Combinatorics/BranchingWalk/` | `MeasureTheory.BranchingWalk` |
| `MeasureTheory/Measure/` | `MeasureTheory` |
| `Probability/PointProcess/` | `ProbabilityTheory` |
| `Probability/BranchingRandomWalk/` | `ProbabilityTheory.BranchingRandomWalk` |

The library target is still called `ThesisSpeed`, so the verification command
remains `lake build ThesisSpeed`; `lakefile.toml` lists the aggregate modules as
the library roots. The project name therefore lives only in the build
configuration and never in a declaration name.

## Placement rules

1. Abstract point-process definitions must not depend on genealogical trees or
   population selection.
2. A general child type must admit the zero measure. Any first-child or
   nonextinction theorem belongs in a law or process file and must state its
   nonempty-support hypothesis.
3. Genealogy contains identities, domains, filtrations, and positions. It does
   not choose the surviving population.
4. Candidate files describe one selection step; process files iterate such a
   step and prove adaptation.
5. `MeasureTheory.UlamHarris`, `MeasureTheory.BranchingWalk` and `MeasureTheory`
   are the deterministic and measure-theoretic layers; they must not import
   `Probability.*`. The abstract point process is itself a random measure, so
   it lives in `Probability/PointProcess/` even though it only speaks the
   measure-theoretic vocabulary; its branching-random-walk realization belongs
   to that domain and stays in `Probability/BranchingRandomWalk/PointProcess/`.
   A filtration, a probability measure, an almost sure statement, or a
   stopping time places a file in `Probability/BranchingRandomWalk`, even when
   its object is a tree or a branch. `Step/Position/Measurability.lean` is the
   model case: the deterministic position definitions stay in
   `Combinatorics/BranchingWalk/Basic/Displace.lean` while their
   generation-filtration measurability lives in the probabilistic file.
6. When a directory grows beyond a small group of closely related files, split
   it by mathematical role as done for `PointProcess`, `Genealogy`, and
   `Population`.
7. When a single file grows past roughly 250 lines, split it along its
   mathematical sublayers rather than by proof length. `Genealogy/` follows
   this rule by construction: definitions, laws, realizations, marks, and
   trees live in separate files, and `RootIndexed/` mirrors the split.
8. A subdirectory name states the role, not the object: `UlamHarris/Basic.lean`
   holds the address objects, `UlamHarris/Tree/Basic.lean` the tree objects,
   `UlamHarris/MarkedTree/Basic.lean` the marked trees,
   `BranchingWalk/Step/Field.lean` the primitive field, and `Exploration/Selected/`
   the population-selection results. A file must not be a single-field wrapper
   around an object defined elsewhere.

`Timing/` currently has seven focused files and does not need another level.

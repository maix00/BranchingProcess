# Lean source layout

The source tree follows the mathematical dependency direction. Files should
stay small enough to have one principal definition or proof layer.

```text
Combinatorics/                deterministic combinatorics
  UlamHarris/                 deterministic address combinatorics
    Basic.lean                TreeNode, GenealogicalTree, MarkedTree, Mark
    Split.lean                the declared-split predicate
  BranchingStep/              deterministic branching-step combinatorics
    Basic.lean                `BranchingStep ι X = ι → Option X` and its σ-algebra
    Prefix.lean               presence-prefix and order conditions on slots
    Increment.lean            increments, support, monotone increments
    Field.lean                primitive step fields
    AccumulatedMark.lean      total path accumulation and its sum bridges
    PartialMark.lean          the `Option` accumulation and its sum bridges
    Realization.lean          which addresses a field realizes
    RealizedTree.lean         realized tree and marked tree
    Position/Basic.lean       the displacement field induced by a step field
    Slot/Basic.lean           `NatRealBranchingStep`, presence, displacement, truncation
    Slot/Order.lean           the ordered slot set
    Slot/Position.lean        positions of addresses on a marked tree
MeasureTheory/                measure-theoretic infrastructure
  Measure/
    FiniteOnFamily.lean       the single finiteness condition and its families
    AtomFiniteness.lean       finite sublevel sets of a finite ENNReal weight
    Domination.lean           a.e. finiteness from an integrable dominator
  PointProcess/
    Basic.lean                general point processes on `E`
Probability/                  anything with a law, a filtration, or an a.e. claim
  BranchingRandomWalk/        the branching random walk, one domain
    Tree/Filtration.lean      generation spaces and the generation filtration
    Step/
      Law.lean                product laws, marginals, and independence
      DisplacementLaw.lean    injectively reindexed displacement independence
      OrderedSupport.lean     ordered support transfers to every address
      Position/Measurability.lean  realized nodes and accumulated marks
      Position/Slot.lean      positions of addresses under the filtration
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
- `𝕍 := TreeNode ℕ` is the Ulam--Harris vertex set `⋃ₙ ℕⁿ` of the paper. Code
  that works with natural-number child labels writes `𝕍`, matching the
  notation of the thesis.
- `GenealogicalTree α` is a deterministic rooted tree of `TreeNode α`
  addresses: a carrier together with the root, prefix, and ordered-sibling
  axioms. `UlamHarrisTree` is the `ℕ`-indexed case. A bare `Set (List α)` is
  only its carrier, never the tree itself.
- `MarkedTree α X` pairs a `GenealogicalTree α` with a mark on each realized
  node.
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
- `BranchingStepField α X` is the primitive field `TreeNode α → BranchingStep α X`
  of branching steps, with address labels and child labels in the same type
  `α`. A slot may be absent, so a field is not itself a tree and is not wrapped
  in a tree-named type. The derived objects are the realized tree
  `branchingRealizedTree`, the accumulated marks `branchingStepAccumulatedMark`
  (the total algebraic extension) and `branchingStepAccumulatedMark?` (partial,
  returning `none` when some slot on the root path is absent), and the marked
  tree `branchingStepMarkedTree`.
  The path recursion carries the current address as an explicit accumulator
  (`branchingStepAccumulatedMarkFrom`, `branchingStepPresentAlong`), so the
  realized tree and the marks never reconstruct an address from a list index;
  the partial mark follows the same skeleton in `Option`
  (`branchingStepAccumulatedMarkFrom?`), so it is a computable definition that
  needs neither `classical` nor a decision procedure for realization. The
  paper's sum over the prefixes of the address is kept as a bridge, in a
  `Finset.range` form and a `Fin.length` form, and for both marks:
  `branchingStepAccumulatedMark_eq_sum`, `branchingStepAccumulatedMark_eq_sum_fin`,
  `branchingStepAccumulatedMark?_eq_some_sum_iff` and
  `branchingStepAccumulatedMark?_eq_some_sum_fin_iff`.

`BranchingStep` is the primitive object and accumulated marks are derived
quantities, so the accumulated marks are named `branchingStepAccumulatedMark`
and `branchingStepAccumulatedMark?` rather than being called paths, trees, or
positions.

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
- `PointProcess Ω E 𝒜` is the abstract point process: a measurable map into
  the space of counting measures on `E` that are finite on `𝒜`. The measurable
  space on `Measure E` is Mathlib's evaluation sigma-algebra from the Giry
  monad. The family is a parameter, so the thesis condition is not hardcoded.
- `BranchingStepPointProcess Ω ι X 𝒜` refines it by a measurable branching
  step whose Dirac sum is the samplewise measure. The thesis specialization is
  `RealBranchingStepPointProcess Ω := BranchingStepPointProcess Ω ℕ ℝ
  (leftRayFamily ℝ)`; swapping in `rightRayFamily ℝ` gives the mirror object
  without touching any other definition.
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

- `Combinatorics/BranchingStep/Slot/` is the target vocabulary, and it is
  deterministic: it needs no probability measure. `BranchingStep ℕ ℝ = ℕ →
  Option ℝ` writes slot `i` as `some x` when the `i`th child is present at
  displacement `x`, and as `none` otherwise. `Slot/Basic.lean` names presence,
  displacement, nonemptiness, and truncation; `Slot/Order.lean` names the
  ordered subset `orderedBranchingSteps`; `Slot/Position.lean` records the
  deterministic position and realization vocabulary. Its measurability under
  the generation filtration is not deterministic and lives in
  `Probability/BranchingRandomWalk/Step/Position/Slot.lean`; the Dirac-sum
  point measure in slot coordinates lives in
  `Probability/BranchingRandomWalk/PointProcess/PointMeasure.lean`.
- `PointProcess/Representation/` is the bridge from an abstract measure-valued
  input to that vocabulary. `MonotoneEnumeration ν rel` is the generic
  structure, with mark type `X` and ordering relation `rel` as parameters;
  `RealLineEnumeration.lean` contains its real-line laws;
  `RankedAtom.lean` builds the canonical ranked atom of a counting measure,
  `RankedAtomLocation.lean` locates each rank, `RankedOrder.lean` records its
  order and nonemptiness, `RankedReconstruction.lean` reconstructs the input
  measure, and `FromMeasure.lean` applies it samplewise.
- `PointProcess/Enumeration/` holds the first/next-atom algorithms for a raw
  mark that is already slot-indexed but not yet ordered by position.
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
| `Combinatorics/UlamHarris/` | `UlamHarris` |
| `Combinatorics/BranchingStep/` | `BranchingStep` |
| `MeasureTheory/` | `MeasureTheory` |
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
5. `Combinatorics.UlamHarris`, `Combinatorics.BranchingStep` and `MeasureTheory`
   are the deterministic and measure-theoretic layers; they must not import
   `Probability.BranchingRandomWalk`. A filtration, a probability measure, an
   almost sure statement, or a stopping time places a file in
   `Probability.BranchingRandomWalk`, even when its object is a tree or a
   branch. `Step/Position/Slot.lean` is the model case: the deterministic
   position definitions stay in `Combinatorics/BranchingStep/Slot/Position.lean`
   while their generation-filtration measurability lives in the probabilistic
   file.
6. When a directory grows beyond a small group of closely related files, split
   it by mathematical role as done for `PointProcess`, `Genealogy`, and
   `Population`.
7. When a single file grows past roughly 250 lines, split it along its
   mathematical sublayers rather than by proof length. `Genealogy/` follows
   this rule by construction: definitions, laws, realizations, marks, and
   trees live in separate files, and `RootIndexed/` mirrors the split.
8. A subdirectory name states the role, not the object: `UlamHarris/Basic.lean`
   holds the tree objects, `BranchingStep/Field.lean` the primitive field, and
   `Exploration/Selected/` the population-selection results. A file must not be
   a single-field wrapper around an object defined elsewhere.

`Timing/` currently has seven focused files and does not need another level.

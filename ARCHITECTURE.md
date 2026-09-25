# Lean source layout

The source tree follows the mathematical dependency direction. Files should
stay small enough to have one principal definition or proof layer.

```text
ThesisSpeed/
  Assumptions/                structural, moment, and theorem-specific bundles
  Probability/
    PointProcess/
      RandomMeasure/          abstract random measures and their Dirac-sum realizations
        Basic.lean            general point processes on `E` and the `ℝ` offspring specialization
        LocalFiniteness.lean  finite sublevel sets and leftmost atoms
        DiracSum.lean         offspring Dirac sums built from mathlib measures
        BranchingStep.lean    point measure induced by a branching-step field
      Representation/         measurable ordered slot representations
        OrderedSlot.lean      bridge from abstract measures to optional slots
        FromMeasure.lean      canonical construction from an abstract measure
      Enumeration/            measurable ordering and coverage
      Law/                    i.i.d. laws and support transfer
      Legacy/                 weighted-slot implementations still being migrated
    Genealogy/
      Tree/
        Basic.lean            TreeNode, GenealogicalTree, MarkedTree, Mark, partial marks
        Filtration.lean       generation spaces, filtration, random-index measurability
        Split.lean            declared splits and their stopping-time property
      BranchingStep/
        Field.lean            the primitive branching-step field
        Law.lean              product laws, marginals, and independence
        AccumulatedMark.lean  the total path accumulation and its sum bridges
        Realization.lean      which addresses a field realizes
        PartialMark.lean      the `Option` accumulation and its sum bridges
        RealizedTree.lean     the realized tree and the marked tree
      Position/
        Basic.lean            displacement field induced by a step field
        Measurability.lean    realized nodes and accumulated marks are observable
      RootIndexed/
        Field.lean            root-indexed step fields and their reindexings
        Law.lean              finite-root product laws and marginals
        Positions.lean        root-indexed marks, positions, and realization
        Filtration.lean       the multi-root step filtration
        Measurability.lean    realized nodes and positions, root by root
      MultiRoot/
        Law.lean              product law over labelled initial ancestors
        Filtration.lean       the multi-root generation filtration
        Realized.lean         realization and positions of labelled descendants
      Reserve/
        Lineages.lean         pre-sampled reserve lineages and their split times
        MultiRoot.lean        the same for every labelled initial root
    Population/
      Candidates/             candidate generation, ordering, leftmost selection, truncation
      Processes/              selected, backbone-truncated, fully truncated processes
      Growth/                 deterministic population-size estimates
    Branching/
      Step.lean               option-valued offspring encoding
      Abstract/               abstract branching-property scaffolding
      RootIndexed/            root-indexed scaffolding
      Selected/               selected subtrees, descendant populations, stopped branching
    Timing/                   stopping times, observability, and counterexamples
  Spine/                      many-to-one ingredients
  Analytic.lean               deterministic closing estimates
```

## Tree and step objects

The words "tree", "marked tree", and "step field" name three different
objects and must not be conflated.

- `TreeNode α` is the abstract address type `List α`. It is a word type over
  the child labels `α` and is not tied to `ℕ`.
- `𝕍 := TreeNode ℕ` is the Ulam--Harris vertex set `⋃ₙ ℕⁿ` of the paper. Code
  that works with natural-number offspring labels writes `𝕍`, matching the
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
  of branching steps, with address labels and offspring labels in the same type
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
- `IsFiniteOnFamily ν 𝒜` in `RandomMeasure/FiniteOnFamily.lean` is the single
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
- `IsLeftLocallyFinite.isFiniteMeasureOnCompacts` shows the paper's left-ray
  condition implies the compact-finiteness axiom on `ℝ`.
- `RandomMeasure/Domination.lean` states the abstract form of the paper's
  derivation: a random measure dominated on a family by an integrable
  functional is a.e. finite on that family. The countable version collects the
  statements into one good event.

## Placement rules

1. Abstract point-process definitions must not depend on genealogical trees or
   population selection.
2. A general offspring type must admit the zero measure. Any first-child or
   nonextinction theorem belongs in a law or process file and must state its
   nonempty-support hypothesis.
3. Genealogy contains identities, domains, filtrations, and positions. It does
   not choose the surviving population.
4. Candidate files describe one selection step; process files iterate such a
   step and prove adaptation.
5. Branching and timing consume the preceding definitions. They must not be
   imported back into the foundational layers.
6. When a directory grows beyond a small group of closely related files, split
   it by mathematical role as done for `PointProcess`, `Genealogy`,
   `Branching`, and `Population`.
7. When a single file grows past roughly 250 lines, split it along its
   mathematical sublayers rather than by proof length. `Genealogy/` follows
   this rule by construction: definitions, laws, realizations, marks, and
   trees live in separate files, and `RootIndexed/` mirrors the split.
8. A subdirectory name states the role, not the object: `Tree/Basic.lean`
   holds the tree objects, `BranchingStep/Field.lean` the primitive field,
   and `Selected/` the population-selection results. A file must not be a
   single-field wrapper around an object defined elsewhere.

`Timing/` currently has four focused files and does not need another level.

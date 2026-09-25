# Lean source layout

The source tree follows the mathematical dependency direction. Files should
stay small enough to have one principal definition or proof layer.

```text
ThesisSpeed/
  Assumptions/                structural, moment, and theorem-specific bundles
  Probability/
    PointProcess/
      Basic.lean              abstract measurable counting measures
      Encoding.lean           optional-slot representation, including zero children
      Measure.lean            Dirac-sum realization using mathlib measures
      Representation.lean     bridge between abstract measures and slots
      LocalFiniteness.lean
      Enumeration/            measurable ordering and coverage
      Law/                    i.i.d. laws and support transfer
    Genealogy/
      Tree.lean               deterministic tree, marked tree, pre-sampled field, filtration
      BranchingStepTree.lean  step fields, realized trees, accumulated marks, laws
      BranchingPositions.lean measurability of realized nodes and accumulated marks
      Positions.lean          displacement field of accumulated marks
      MultiRoot.lean          several labelled initial ancestors
      Reserve.lean            reserve lineages and exploration paths
      FirstSplit.lean         first observable split
      RootIndexed/            root-indexed positions, filtration, and laws
    Population/
      Candidates/             candidate generation, ranking, finite truncation
      Processes/              selected, backbone-truncated, fully truncated processes
      Growth/                 deterministic population-size estimates
    Branching/                subtree independence and branching properties
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

`BranchingStep` is the primitive object and accumulated marks are derived
quantities, so the accumulated marks are named `branchingStepAccumulatedMark`
and `branchingStepAccumulatedMark?` rather than being called paths, trees, or
positions.

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
6. When a directory grows beyond a small group of closely related files,
   split it by mathematical role as done for `PointProcess` and `Population`.

The next planned split is `Branching/`: fixed-root results, random-root
results, and multi-root results will become subdirectories when new stopped
or stopping-line theorems are added. Moving the current seven files before
that boundary would add import churn without clarifying a new dependency
layer. `Timing/` currently has four focused files and does not need another
level.

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.Definitions

/-!
# Root-indexed branching step fields

An arbitrary type `Root` indexes the initial ancestors. Each label owns its own
step field over the Ulam--Harris addresses, and reindexing along a map
`f : NewRoot → Root` relabels the roots. The `Fin m` and `ℕ` specializations
are the finite and countable cases used by the population arguments.

The public declarations are:

* `ProbabilityTheory.BranchingRandomWalk.RootIndexed.StepField Root α X` is
  `Root → Combinatorics.Branching.StepField α X`;
  `ProbabilityTheory.BranchingRandomWalk.FiniteRootStepField m α X` and
  `ProbabilityTheory.BranchingRandomWalk.CountableRootStepField α X` use
  `Root = Fin m` and `Root = ℕ`.
* `ProbabilityTheory.BranchingRandomWalk.RootIndexed.StepField.reindex f step`
  relabels the root coordinate, with `(step.reindex f) r = step (f r)`.
* `ProbabilityTheory.BranchingRandomWalk.RootIndexed.StepField.reindexCoordinates
  f step` pulls the field back along
  `f : NewRoot × TreeNode α → Root × TreeNode α`, so
  `(step.reindexCoordinates f) r u = step (f (r, u)).1 (f (r, u)).2`.
  `ProbabilityTheory.BranchingRandomWalk.RootIndexed.StepField.reindexCoordinates_apply`
  gives this formula. Its generic representation is
  `Function.curry (Function.uncurry step ∘ f)`.
* `ProbabilityTheory.BranchingRandomWalk.RootIndexed.StepField.reindex_eq_reindexCoordinates`
  identifies root relabelling with coordinate relabelling that keeps
  addresses fixed. `ProbabilityTheory.BranchingRandomWalk.RootIndexed.StepField.first
  m step` is `step.reindex Fin.val`; `ProbabilityTheory.BranchingRandomWalk.FiniteRootStepField.first
  h step` is `step.reindex (Fin.castLE h)` when `h : m ≤ n`.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


namespace RootIndexed

abbrev StepField (Root α X : Type*) :=
  Root → Combinatorics.Branching.StepField α X

end RootIndexed

abbrev FiniteRootStepField (m : ℕ) (α X : Type*) :=
  RootIndexed.StepField (Fin m) α X

abbrev CountableRootStepField (α X : Type*) :=
  RootIndexed.StepField ℕ α X

namespace RootIndexed.StepField

def reindex {Root NewRoot α X : Type*} (f : NewRoot → Root)
    (step : RootIndexed.StepField Root α X) :
    RootIndexed.StepField NewRoot α X :=
  fun r => step (f r)

/-- Pull a root-indexed field back along a map of complete coordinates.  In
contrast with `reindex`, this may send different addresses of one new root to
different source roots.  No probabilistic condition is built into the
definition; injectivity is imposed only by the product-law theorem. -/
def reindexCoordinates {Root NewRoot α X : Type*}
    (f : NewRoot × TreeNode α → Root × TreeNode α)
    (step : RootIndexed.StepField Root α X) :
    RootIndexed.StepField NewRoot α X :=
  fun r u => step (f (r, u)).1 (f (r, u)).2

@[simp] theorem reindexCoordinates_apply
    {Root NewRoot α X : Type*}
    (f : NewRoot × TreeNode α → Root × TreeNode α)
    (step : RootIndexed.StepField Root α X)
    (r : NewRoot) (u : TreeNode α) :
    step.reindexCoordinates f r u =
      step (f (r, u)).1 (f (r, u)).2 :=
  rfl

/-- Root relabelling is the coordinate relabelling that leaves every address
unchanged. -/
theorem reindex_eq_reindexCoordinates
    {Root NewRoot α X : Type*} (f : NewRoot → Root)
    (step : RootIndexed.StepField Root α X) :
    step.reindex f =
      step.reindexCoordinates (fun p => (f p.1, p.2)) := by
  rfl

def first {α X : Type*} (m : ℕ) (step : CountableRootStepField α X) :
    FiniteRootStepField m α X :=
  step.reindex Fin.val

end RootIndexed.StepField

def FiniteRootStepField.first
    {α X : Type*} {m n : ℕ} (h : m ≤ n)
    (step : FiniteRootStepField n α X) :
    FiniteRootStepField m α X :=
  step.reindex (Fin.castLE h)

end ProbabilityTheory.BranchingRandomWalk

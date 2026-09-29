module

public import Combinatorics.BranchingWalk.Basic.Definitions

/-!
# Root-indexed branching step fields

An arbitrary type `Root` indexes the initial ancestors. Each label owns its own
step field over the Ulam--Harris addresses, and reindexing along a map
`f : NewRoot → Root` relabels the roots. The `Fin m` and `ℕ` instances are the
finite and countable cases used by the population arguments.
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

@[simp] theorem reindexCoordinates_id
    {Root α X : Type*} (step : RootIndexed.StepField Root α X) :
    step.reindexCoordinates id = step := by
  rfl

theorem reindexCoordinates_comp
    {Root MiddleRoot NewRoot α X : Type*}
    (f : MiddleRoot × TreeNode α → Root × TreeNode α)
    (g : NewRoot × TreeNode α → MiddleRoot × TreeNode α)
    (step : RootIndexed.StepField Root α X) :
    (step.reindexCoordinates f).reindexCoordinates g =
      step.reindexCoordinates (f ∘ g) := by
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

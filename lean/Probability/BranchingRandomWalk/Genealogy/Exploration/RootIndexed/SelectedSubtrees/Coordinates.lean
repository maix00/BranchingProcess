import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Iteration
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Position

/-!
# Original coordinates of iterated selected subtrees

Every finite adaptive subtree replacement is accompanied by a cumulative
root/address map back into the original field.  Both the step coordinates and
absolute positions are preserved exactly.
-/

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

/-- Cumulative original root and address of a root after finitely many
adaptive subtree replacements. -/
def RootIndexed.iteratedSelectedRoots
    {Root α X : Type*}
    (chosen : ℕ → RootIndexed.StepField Root α X →
      Root → Root × TreeNode α) :
    ℕ → RootIndexed.StepField Root α X → Root → Root × TreeNode α
  | 0, _, i => (i, [])
  | j + 1, step, i =>
      let current := chosen j
        (RootIndexed.iteratedSelectedSubtreeStepField chosen j step) i
      let previous := RootIndexed.iteratedSelectedRoots chosen j step current.1
      (previous.1, previous.2 ++ current.2)

@[simp] theorem RootIndexed.iteratedSelectedRoots_zero
    {Root α X : Type*}
    (chosen : ℕ → RootIndexed.StepField Root α X →
      Root → Root × TreeNode α)
    (step : RootIndexed.StepField Root α X) (i : Root) :
    RootIndexed.iteratedSelectedRoots chosen 0 step i = (i, []) :=
  rfl

/-- Reading the iterated field is exactly reading the corresponding rebased
coordinate of the original field. -/
theorem RootIndexed.iteratedSelectedSubtreeStepField_apply
    {Root α X : Type*}
    (chosen : ℕ → RootIndexed.StepField Root α X →
      Root → Root × TreeNode α) :
    ∀ j (step : RootIndexed.StepField Root α X) (i : Root)
      (v : TreeNode α),
      RootIndexed.iteratedSelectedSubtreeStepField chosen j step i v =
        step (RootIndexed.iteratedSelectedRoots chosen j step i).1
          ((RootIndexed.iteratedSelectedRoots chosen j step i).2 ++ v) := by
  intro j
  induction j with
  | zero =>
      intro step i v
      rfl
  | succ j ih =>
      intro step i v
      simp only [RootIndexed.iteratedSelectedSubtreeStepField_succ,
        Function.comp_apply, RootIndexed.selectedSubtreeStepFieldVector,
        RootIndexed.subtreeStepFieldVector]
      rw [ih]
      simp only [RootIndexed.iteratedSelectedRoots, List.append_assoc]

/-- Absolute initial positions of the iterated roots, expressed directly in
the original field. -/
def RootIndexed.iteratedSelectedInitialPosition
    {Root α Mark Position : Type*} [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position)
    (chosen : ℕ → RootIndexed.StepField Root α Mark →
      Root → Root × TreeNode α)
    (j : ℕ) (step : RootIndexed.StepField Root α Mark) : Root → Position :=
  fun i =>
    let original := RootIndexed.iteratedSelectedRoots chosen j step i
    RootIndexed.position initial d step original.1 original.2

/-- Iteration preserves every absolute position after translating the new
root to its cumulative original position. -/
theorem RootIndexed.position_iteratedSelectedSubtreeStepField
    {Root α Mark Position : Type*} [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position)
    (chosen : ℕ → RootIndexed.StepField Root α Mark →
      Root → Root × TreeNode α)
    (j : ℕ) (step : RootIndexed.StepField Root α Mark)
    (i : Root) (v : TreeNode α) :
    RootIndexed.position
        (RootIndexed.iteratedSelectedInitialPosition initial d chosen j step) d
        (RootIndexed.iteratedSelectedSubtreeStepField chosen j step) i v =
      RootIndexed.position initial d step
        (RootIndexed.iteratedSelectedRoots chosen j step i).1
        ((RootIndexed.iteratedSelectedRoots chosen j step i).2 ++ v) := by
  let original := RootIndexed.iteratedSelectedRoots chosen j step i
  have hfield :
      (RootIndexed.iteratedSelectedSubtreeStepField chosen j step) i =
        fun w => step original.1 (original.2 ++ w) := by
    funext w
    exact RootIndexed.iteratedSelectedSubtreeStepField_apply
      chosen j step i w
  rw [RootIndexed.position_append]
  unfold RootIndexed.iteratedSelectedInitialPosition
  change RootIndexed.position initial d step original.1 original.2 +
      Combinatorics.Branching.displaceWith d
        ((RootIndexed.iteratedSelectedSubtreeStepField chosen j step) i) [] v =
    _
  rw [hfield]

end ProbabilityTheory.BranchingRandomWalk

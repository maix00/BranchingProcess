import ThesisSpeed.Probability.Genealogy.Tree
import ThesisSpeed.Probability.Branching.Step
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory

namespace ThesisSpeed

/-! A marked tree is a node-indexed branching-step field together with its
induced cumulative position mark. -/
def branchingTreePathSum {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) (u : TreeNode) : X :=
  ∑ j ∈ Finset.range u.length,
    branchingStepIncrement (ω (u.take j)) (u[j]!)

structure BranchingMarkedTree (X : Type*) [AddCommMonoid X] where
  step : TreeNode → BranchingStep ℕ X
  mark : TreeNode → X
  mark_eq_pathSum : ∀ u, mark u = branchingTreePathSum step u

def BranchingMarkedTree.ofStep {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) : BranchingMarkedTree X where
  step := step
  mark := branchingTreePathSum step
  mark_eq_pathSum := fun _ => rfl

@[simp] theorem BranchingMarkedTree.ofStep_step
    {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) :
    (BranchingMarkedTree.ofStep step).step = step := rfl

@[simp] theorem BranchingMarkedTree.ofStep_mark
    {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) :
    (BranchingMarkedTree.ofStep step).mark = branchingTreePathSum step := rfl

abbrev RandomBranchingMarkedTree (Ω X : Type*) [AddCommMonoid X] :=
  Ω → BranchingMarkedTree X

noncomputable def branchingStepFieldLaw {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) :
    Measure (TreeNode → BranchingStep ℕ X) :=
  Measure.infinitePi (fun _ : TreeNode => μ)

instance branchingStepFieldLaw.isProbabilityMeasure
    {X : Type*} [MeasurableSpace X] (μ : Measure (BranchingStep ℕ X))
    [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (branchingStepFieldLaw μ) := by
  unfold branchingStepFieldLaw
  infer_instance

theorem branchingStepFieldLaw_coordinate
    {X : Type*} [MeasurableSpace X] (μ : Measure (BranchingStep ℕ X))
    [IsProbabilityMeasure μ] (u : TreeNode) :
    (branchingStepFieldLaw μ).map (fun ω => ω u) = μ := by
  unfold branchingStepFieldLaw
  exact Measure.infinitePi_map_eval (fun _ : TreeNode => μ) u

theorem branchingTreePathSum_nil {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) :
    branchingTreePathSum ω [] = 0 := by simp [branchingTreePathSum]

theorem branchingTreePathSum_singleton {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) (i : ℕ) :
    branchingTreePathSum ω [i] = branchingStepIncrement (ω []) i := by
  simp [branchingTreePathSum]

abbrev PositionMarkedTree (X : Type*) := TreeNode → X

def positionMarkedTree {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) : PositionMarkedTree X :=
  branchingTreePathSum ω

def randomPositionMarkedTree {Ω X : Type*} [AddCommMonoid X]
    (ω : RandomBranchingMarkedTree Ω X) : Ω → PositionMarkedTree X :=
  fun z => (ω z).mark

theorem positionMarkedTree_at_root {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) :
    positionMarkedTree ω [] = 0 := by
  simp [positionMarkedTree, branchingTreePathSum]

end ThesisSpeed

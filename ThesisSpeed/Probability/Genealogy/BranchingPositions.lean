import ThesisSpeed.Probability.Genealogy.MarkedTree

/-!
# Positions induced by abstract branching steps

This file is the abstract replacement for the old weighted-slot position
definitions.  A node position is the sum of the step increments along its
root path; no point-process or survival convention is involved here.
-/

namespace ThesisSpeed

def branchingNodePosition {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) (u : TreeNode) : X :=
  branchingTreePathSum step u

@[simp] theorem branchingNodePosition_eq_pathSum
    {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) (u : TreeNode) :
    branchingNodePosition step u = branchingTreePathSum step u := rfl

theorem branchingNodePosition_nil
    {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) :
  branchingNodePosition step [] = 0 := by
  exact branchingTreePathSum_nil step

theorem branchingNodePosition_append_singleton
    {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) (u : TreeNode) (i : ℕ) :
    branchingNodePosition step (u ++ [i]) =
      branchingNodePosition step u +
        branchingStepIncrement (step u) i := by
  exact branchingTreePathSum_append_singleton step u i

def branchingRealizedNode {X : Type*}
    (step : TreeNode → BranchingStep ℕ X) (u : TreeNode) : Prop :=
  ∀ j ∈ Finset.range u.length,
    branchingStepPresent (step (u.take j)) (u[j]!)

theorem branchingRealizedNode_nil {X : Type*}
    (step : TreeNode → BranchingStep ℕ X) :
    branchingRealizedNode step [] := by
  simp [branchingRealizedNode]

theorem branchingRealizedNode_append_singleton_iff
    {X : Type*} (step : TreeNode → BranchingStep ℕ X)
    (u : TreeNode) (i : ℕ) :
    branchingRealizedNode step (u ++ [i]) ↔
      branchingRealizedNode step u ∧
        branchingStepPresent (step u) i := by
  constructor
  · intro h
    constructor
    · intro j hj
      have hjlt : j < u.length := Finset.mem_range.mp hj
      have hpath := h j (by
        apply Finset.mem_range.mpr
        simpa using Nat.lt_succ_of_lt hjlt)
      simpa [List.take_append_of_le_length (Nat.le_of_lt hjlt),
        List.getElem?_append_left hjlt] using hpath
    · have hlast := h u.length (by simp)
      simpa using hlast
  · rintro ⟨hu, hi⟩ j hj
    by_cases hju : j < u.length
    · have hpath := hu j (Finset.mem_range.mpr hju)
      simpa [List.take_append_of_le_length (Nat.le_of_lt hju),
        List.getElem?_append_left hju] using hpath
    · have hj_eq : j = u.length := by
        have hj_le : j ≤ u.length := by
          simpa [List.length_append] using hj
        omega
      subst j
      simpa using hi

theorem branchingRealizedNode_append_iff
    {X : Type*} (step : TreeNode → BranchingStep ℕ X)
    (u v : TreeNode) :
    branchingRealizedNode step (u ++ v) ↔
      branchingRealizedNode step u ∧
        branchingRealizedNode (fun w => step (u ++ w)) v := by
  induction v using List.reverseRecOn with
  | nil => simp [branchingRealizedNode]
  | append_singleton v i ih =>
      rw [← List.append_assoc u v [i]]
      rw [branchingRealizedNode_append_singleton_iff]
      rw [ih]
      rw [branchingRealizedNode_append_singleton_iff]
      simp only [and_assoc]

end ThesisSpeed

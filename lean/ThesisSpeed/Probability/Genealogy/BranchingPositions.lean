import ThesisSpeed.Probability.Genealogy.MarkedTree

/-!
# Positions induced by abstract branching steps

This file is the abstract replacement for the old weighted-slot position
definitions.  A node position is the sum of the step increments along its
root path; no point-process or survival convention is involved here.
-/

namespace ThesisSpeed

open MeasureTheory

def branchingNodeDisplacement {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) (u : TreeNode) : X :=
  branchingTreePathSum step u

@[simp] theorem branchingNodeDisplacement_eq_pathSum
    {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) (u : TreeNode) :
    branchingNodeDisplacement step u = branchingTreePathSum step u := rfl

theorem branchingNodeDisplacement_nil
    {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) :
  branchingNodeDisplacement step [] = 0 := by
  exact branchingTreePathSum_nil step

theorem branchingNodeDisplacement_append_singleton
    {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) (u : TreeNode) (i : ℕ) :
    branchingNodeDisplacement step (u ++ [i]) =
      branchingNodeDisplacement step u +
        branchingStepIncrement (step u) i := by
  exact branchingTreePathSum_append_singleton step u i

def branchingRealizedNode {X : Type*}
    (step : TreeNode → BranchingStep ℕ X) (u : TreeNode) : Prop :=
  ∀ j ∈ Finset.range u.length,
    branchingStepPresent (step (u.take j)) (u[j]!)

/-! Partial position interface; the total path sum remains available for
    algebraic manipulations. -/
noncomputable def branchingTreePathSum? {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) (u : TreeNode) : Option X :=
  by classical
     exact if h : branchingRealizedNode step u then
       some (branchingTreePathSum step u) else none

theorem branchingTreePathSum?_eq_some_iff
    {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) (u : TreeNode) :
    branchingTreePathSum? step u = some (branchingTreePathSum step u) ↔
      branchingRealizedNode step u := by
  classical
  by_cases h : branchingRealizedNode step u <;> simp [branchingTreePathSum?, h]

@[simp] theorem branchingTreePathSum?_nil
    {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) :
    branchingTreePathSum? step [] = some 0 := by
  classical
  simp [branchingTreePathSum?, branchingRealizedNode,
    branchingTreePathSum_nil]

noncomputable def branchingNodeDisplacement? {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) (u : TreeNode) : Option X :=
  branchingTreePathSum? step u

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

theorem branchingRealizedNode_measurableSet
    {X : Type*} [MeasurableSpace X] (u : TreeNode) :
    MeasurableSet[generationFiltration (Mark := BranchingStep ℕ X) u.length]
      {step : TreeNode → BranchingStep ℕ X |
        branchingRealizedNode step u} := by
  have hset : {step : TreeNode → BranchingStep ℕ X |
      branchingRealizedNode step u} =
      ⋂ j ∈ Finset.range u.length,
        {step : TreeNode → BranchingStep ℕ X |
          branchingStepPresent (step (u.take j)) (u[j]!)} := by
    ext step
    simp [branchingRealizedNode]
  rw [hset]
  apply Finset.measurableSet_biInter
  intro j hj
  have hjlt : j < u.length := Finset.mem_range.mp hj
  have hprefix : (u.take j).length < u.length := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hjlt), hjlt]
  exact (mark_measurable_of_depth_lt (Mark := BranchingStep ℕ X)
    (u.take j) u.length hprefix)
      (branchingStepPresent_measurableSet (X := X) (u[j]!))

theorem branchingNodeDisplacement_real_measurable (u : TreeNode) :
    Measurable[generationFiltration
      (Mark := BranchingStep ℕ ℝ) u.length]
      (fun step => branchingNodeDisplacement step u) := by
  unfold branchingNodeDisplacement branchingTreePathSum
  apply Finset.measurable_fun_sum
  intro j hj
  have hjlt : j < u.length := Finset.mem_range.mp hj
  have hprefix : (u.take j).length < u.length := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hjlt), hjlt]
  exact (branchingStepIncrement_measurable (X := ℝ) (u[j]!)).comp
    (mark_measurable_of_depth_lt (Mark := BranchingStep ℕ ℝ)
      (u.take j) u.length hprefix)

def branchingDisplacementAtGeneration (n : ℕ) (u : TreeNode)
    (step : TreeNode → BranchingStep ℕ ℝ) : ℝ :=
  if u.length = n then branchingNodeDisplacement step u else 0

theorem branchingDisplacementAtGeneration_measurable (n : ℕ) (u : TreeNode) :
    Measurable[generationFiltration (Mark := BranchingStep ℕ ℝ) n]
      (branchingDisplacementAtGeneration n u) := by
  change Measurable[generationFiltration (Mark := BranchingStep ℕ ℝ) n]
    (fun step => if u.length = n then branchingNodeDisplacement step u else 0)
  by_cases hu : u.length = n
  · subst n
    simpa using branchingNodeDisplacement_real_measurable u
  · simp only [hu, ite_false]
    exact measurable_const

set_option linter.style.haveILetI false in
theorem selectedBranchingNodeDisplacement_real_measurable
    (n : ℕ)
    (chosen : (TreeNode → BranchingStep ℕ ℝ) → TreeNode)
    (hchosen : Measurable[
      generationFiltration (Mark := BranchingStep ℕ ℝ) n] chosen)
    (hdepth : ∀ step, (chosen step).length = n) :
    Measurable[generationFiltration (Mark := BranchingStep ℕ ℝ) n]
      (fun step => branchingNodeDisplacement step (chosen step)) := by
  letI : MeasurableSpace (TreeNode → BranchingStep ℕ ℝ) :=
    generationFiltration (Mark := BranchingStep ℕ ℝ) n
  have hjoint : Measurable
      (fun p : TreeNode × (TreeNode → BranchingStep ℕ ℝ) =>
        branchingDisplacementAtGeneration n p.1 p.2) :=
    measurable_from_prod_countable_right
      (branchingDisplacementAtGeneration_measurable n)
  have h := hjoint.comp (hchosen.prodMk measurable_id)
  convert h using 1
  funext step
  simp [branchingDisplacementAtGeneration, hdepth step]

end ThesisSpeed

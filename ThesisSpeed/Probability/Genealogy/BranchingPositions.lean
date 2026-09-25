import ThesisSpeed.Probability.Genealogy.BranchingStepTree

/-!
# Measurability of realized nodes and accumulated marks

A realized node is observable at its own generation, and the accumulated mark
of a fixed or generation-measurably selected node is adapted. The step-field
object and the accumulated marks themselves live in `BranchingStepTree.lean`;
this file only contains the measurability results.
-/

open MeasureTheory

namespace ThesisSpeed

theorem branchingRealizedNode_measurableSet {X : Type*} [MeasurableSpace X]
    (u : TreeNode) :
    MeasurableSet[generationFiltration (Mark := BranchingStep ℕ X) u.length]
      {step : BranchingStepField X | branchingRealizedNode step u} := by
  have hset : {step : BranchingStepField X |
      branchingRealizedNode step u} =
      ⋂ j ∈ Finset.range u.length,
        {step : BranchingStepField X |
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

theorem branchingStepAccumulatedMark_real_measurable (u : TreeNode) :
    Measurable[generationFiltration (Mark := BranchingStep ℕ ℝ) u.length]
      (fun step : BranchingStepField ℝ =>
        branchingStepAccumulatedMark step u) := by
  unfold branchingStepAccumulatedMark
  apply Finset.measurable_fun_sum
  intro j hj
  have hjlt : j < u.length := Finset.mem_range.mp hj
  have hprefix : (u.take j).length < u.length := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hjlt), hjlt]
  exact (branchingStepIncrement_measurable (X := ℝ) (u[j]!)).comp
    (mark_measurable_of_depth_lt (Mark := BranchingStep ℕ ℝ)
      (u.take j) u.length hprefix)

/-- Position of a fixed address once the observed generation matches its
depth, and zero before that. -/
def branchingStepPositionAtGeneration (n : ℕ) (u : TreeNode)
    (step : BranchingStepField ℝ) : ℝ :=
  if u.length = n then branchingStepAccumulatedMark step u else 0

theorem branchingStepPositionAtGeneration_measurable
    (n : ℕ) (u : TreeNode) :
    Measurable[generationFiltration (Mark := BranchingStep ℕ ℝ) n]
      (branchingStepPositionAtGeneration n u) := by
  change Measurable[generationFiltration (Mark := BranchingStep ℕ ℝ) n]
    (fun step : BranchingStepField ℝ =>
      if u.length = n then branchingStepAccumulatedMark step u else 0)
  by_cases hu : u.length = n
  · subst n
    simpa using branchingStepAccumulatedMark_real_measurable u
  · simp only [hu, ite_false]
    exact measurable_const

set_option linter.style.haveILetI false in
theorem selectedBranchingStepPosition_real_measurable
    (n : ℕ)
    (chosen : BranchingStepField ℝ → TreeNode)
    (hchosen : Measurable[
      generationFiltration (Mark := BranchingStep ℕ ℝ) n] chosen)
    (hdepth : ∀ step, (chosen step).length = n) :
    Measurable[generationFiltration (Mark := BranchingStep ℕ ℝ) n]
      (fun step => branchingStepAccumulatedMark step (chosen step)) := by
  letI : MeasurableSpace (BranchingStepField ℝ) :=
    generationFiltration (Mark := BranchingStep ℕ ℝ) n
  have hjoint : Measurable
      (fun p : TreeNode × BranchingStepField ℝ =>
        branchingStepPositionAtGeneration n p.1 p.2) :=
    measurable_from_prod_countable_right
      (branchingStepPositionAtGeneration_measurable n)
  have h := hjoint.comp (hchosen.prodMk measurable_id)
  convert h using 1
  funext step
  simp [branchingStepPositionAtGeneration, hdepth step]

end ThesisSpeed

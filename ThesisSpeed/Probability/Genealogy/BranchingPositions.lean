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

/-- Realization along a remaining path is observable as soon as the whole path
has been revealed. The induction is on the path; the address is carried along
so each step only needs the mark at one fixed address. -/
theorem branchingStepPresentAlong_measurableSet {X : Type*} [MeasurableSpace X]
    (v p : 𝕍) (n : ℕ) (hn : v.length + p.length ≤ n) :
    MeasurableSet[generationFiltration (M := BranchingStep ℕ X) n]
      {step : BranchingStepField ℕ X | branchingStepPresentAlong step v p} := by
  induction p generalizing v with
  | nil =>
      have hset : {step : BranchingStepField ℕ X |
          branchingStepPresentAlong step v []} = Set.univ := by
        ext step
        simp
      rw [hset]
      exact MeasurableSet.univ
  | cons i p ih =>
      have hlen : (v ++ [i]).length = v.length + 1 := by simp
      have hlen' : (i :: p).length = p.length + 1 := by simp
      have hset : {step : BranchingStepField ℕ X |
          branchingStepPresentAlong step v (i :: p)} =
          {step : BranchingStepField ℕ X | branchingStepPresent (step v) i} ∩
            {step : BranchingStepField ℕ X |
              branchingStepPresentAlong step (v ++ [i]) p} := by
        ext step
        simp [branchingStepPresentAlong]
      rw [hset]
      refine MeasurableSet.inter ?_ ?_
      · exact (mark_measurable_of_depth_lt (M := BranchingStep ℕ X) v n
          (by omega))
          (branchingStepPresent_measurableSet (X := X) i)
      · exact ih (v := v ++ [i]) (by omega)

theorem branchingRealizedNode_measurableSet {X : Type*} [MeasurableSpace X]
    (u : 𝕍) :
    MeasurableSet[generationFiltration (M := BranchingStep ℕ X) u.length]
      {step : BranchingStepField ℕ X | branchingRealizedNode step u} := by
  change MeasurableSet[generationFiltration (M := BranchingStep ℕ X) u.length]
    {step : BranchingStepField ℕ X | branchingStepPresentAlong step [] u}
  exact branchingStepPresentAlong_measurableSet (X := X) [] u u.length (by simp)

/-- The accumulated mark is observable at the generation reached by the path;
again the induction carries the current address. -/
theorem branchingStepAccumulatedMarkFrom_real_measurable (v p : 𝕍) (n : ℕ)
    (hn : v.length + p.length ≤ n) :
    Measurable[generationFiltration (M := BranchingStep ℕ ℝ) n]
      (fun step : BranchingStepField ℕ ℝ =>
        branchingStepAccumulatedMarkFrom step v p) := by
  induction p generalizing v with
  | nil => exact measurable_const
  | cons i p ih =>
      have hlen : (v ++ [i]).length = v.length + 1 := by simp
      have hlen' : (i :: p).length = p.length + 1 := by simp
      have hstep : Measurable[generationFiltration (M := BranchingStep ℕ ℝ) n]
          (fun step : BranchingStepField ℕ ℝ => branchingStepIncrement (step v) i) :=
        (branchingStepIncrement_measurable (X := ℝ) i).comp
          (mark_measurable_of_depth_lt (M := BranchingStep ℕ ℝ) v n
            (by omega))
      have hrec : Measurable[generationFiltration (M := BranchingStep ℕ ℝ) n]
          (fun step : BranchingStepField ℕ ℝ =>
            branchingStepAccumulatedMarkFrom step (v ++ [i]) p) :=
        ih (v := v ++ [i]) (by omega)
      change Measurable[generationFiltration (M := BranchingStep ℕ ℝ) n]
        ((fun step : BranchingStepField ℕ ℝ => branchingStepIncrement (step v) i) +
          fun step => branchingStepAccumulatedMarkFrom step (v ++ [i]) p)
      exact hstep.add hrec

theorem branchingStepAccumulatedMark_real_measurable (u : 𝕍) :
    Measurable[generationFiltration (M := BranchingStep ℕ ℝ) u.length]
      (fun step : BranchingStepField ℕ ℝ =>
        branchingStepAccumulatedMark step u) := by
  change Measurable[generationFiltration (M := BranchingStep ℕ ℝ) u.length]
    (fun step : BranchingStepField ℕ ℝ => branchingStepAccumulatedMarkFrom step [] u)
  exact branchingStepAccumulatedMarkFrom_real_measurable [] u u.length (by simp)

/-- Position of a fixed address once the observed generation matches its
depth, and zero before that. -/
def branchingStepPositionAtGeneration (n : ℕ) (u : 𝕍)
    (step : BranchingStepField ℕ ℝ) : ℝ :=
  if u.length = n then branchingStepAccumulatedMark step u else 0

theorem branchingStepPositionAtGeneration_measurable
    (n : ℕ) (u : 𝕍) :
    Measurable[generationFiltration (M := BranchingStep ℕ ℝ) n]
      (branchingStepPositionAtGeneration n u) := by
  change Measurable[generationFiltration (M := BranchingStep ℕ ℝ) n]
    (fun step : BranchingStepField ℕ ℝ =>
      if u.length = n then branchingStepAccumulatedMark step u else 0)
  by_cases hu : u.length = n
  · subst n
    simpa using branchingStepAccumulatedMark_real_measurable u
  · simp only [hu, ite_false]
    exact measurable_const

set_option linter.style.haveILetI false in
theorem selectedBranchingStepPosition_real_measurable
    (n : ℕ)
    (chosen : BranchingStepField ℕ ℝ → 𝕍)
    (hchosen : Measurable[
      generationFiltration (M := BranchingStep ℕ ℝ) n] chosen)
    (hdepth : ∀ step, (chosen step).length = n) :
    Measurable[generationFiltration (M := BranchingStep ℕ ℝ) n]
      (fun step => branchingStepAccumulatedMark step (chosen step)) := by
  letI : MeasurableSpace (BranchingStepField ℕ ℝ) :=
    generationFiltration (M := BranchingStep ℕ ℝ) n
  have hjoint : Measurable
      (fun p : 𝕍 × BranchingStepField ℕ ℝ =>
        branchingStepPositionAtGeneration n p.1 p.2) :=
    measurable_from_prod_countable_right
      (branchingStepPositionAtGeneration_measurable n)
  have h := hjoint.comp (hchosen.prodMk measurable_id)
  convert h using 1
  funext step
  simp [branchingStepPositionAtGeneration, hdepth step]

end ThesisSpeed

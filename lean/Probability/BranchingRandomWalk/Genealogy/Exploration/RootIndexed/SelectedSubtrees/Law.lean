import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Factorization

/-!
# Law and independence of the selected subtree vector

The selected descendant fields retain the product law of fresh independent
branching-step fields and are independent of the generation filtration.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory


theorem selectedMultiRootSubtreeStepFieldVector_law
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ}
    (chosen : FiniteRootBranchingStepField m X → Fin k → Fin m × 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen)
    (hdepth : ∀ step j, (chosen step j).2.length = n)
    (hinj : ∀ step, Function.Injective (chosen step)) :
    (finiteRootBranchingStepFieldLaw μ m).map
        (selectedMultiRootSubtreeStepFieldVector chosen) =
      Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ) := by
  ext B hB
  rw [Measure.map_apply
    (selectedMultiRootSubtreeStepFieldVector_measurable chosen hchosen) hB]
  have h := selectedMultiRootSubtreeStepFieldVector_event_factorization μ
    chosen hchosen hdepth hinj Set.univ B (by simp) hB
  simpa using h

theorem selectedMultiRootSubtreeStepFieldVector_independent
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ}
    (chosen : FiniteRootBranchingStepField m X → Fin k → Fin m × 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen)
    (hdepth : ∀ step j, (chosen step j).2.length = n)
    (hinj : ∀ step, Function.Injective (chosen step)) :
    Indep (multiRootStepFiltration (m := m) (X := X) n)
      (MeasurableSpace.comap
        (selectedMultiRootSubtreeStepFieldVector chosen) inferInstance)
      (finiteRootBranchingStepFieldLaw μ m) := by
  apply (indep_iff_forall_indepSet (finiteRootBranchingStepFieldLaw μ m)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  apply (indepSet_iff_measure_inter_eq_mul
    ((multiRootStepFiltration (m := m) (X := X) |>.le n) _ hA)
    ((selectedMultiRootSubtreeStepFieldVector_measurable chosen hchosen) hB)
    (finiteRootBranchingStepFieldLaw μ m)).2
  have hmap : finiteRootBranchingStepFieldLaw μ m
      (selectedMultiRootSubtreeStepFieldVector chosen ⁻¹' B) =
      (Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ)) B := by
    rw [← Measure.map_apply
      (selectedMultiRootSubtreeStepFieldVector_measurable chosen hchosen) hB,
      selectedMultiRootSubtreeStepFieldVector_law μ chosen hchosen
        hdepth hinj]
  rw [hmap]
  exact selectedMultiRootSubtreeStepFieldVector_event_factorization μ chosen
    hchosen hdepth hinj A B hA hB

end ProbabilityTheory.BranchingRandomWalk

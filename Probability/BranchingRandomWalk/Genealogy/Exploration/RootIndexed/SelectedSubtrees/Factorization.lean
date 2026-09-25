import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Cell

/-!
# Factorization for selected subtree events

Partitioning by the countable root vector turns factorization on each cell
into factorization for the selected subtree vector itself.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory


theorem selectedMultiRootSubtreeStepFieldVector_event_factorization
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ}
    (chosen : FiniteRootStepField m X → Fin k → Fin m × 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen)
    (hdepth : ∀ step j, (chosen step j).2.length = n)
    (hinj : ∀ step, Function.Injective (chosen step))
    (A : Set (FiniteRootStepField m X))
    (B : Set (Fin k → 𝕍 → Step ℕ X))
    (hA : MeasurableSet[
      multiRootStepFiltration (m := m) (X := X) n] A)
    (hB : MeasurableSet B) :
    finiteRootStepFieldLaw μ m
        (A ∩ selectedMultiRootSubtreeStepFieldVector chosen ⁻¹' B) =
      finiteRootStepFieldLaw μ m A *
        (Measure.infinitePi (fun _ : Fin k => stepFieldLaw μ)) B := by
  let P := finiteRootStepFieldLaw μ m
  let Q := Measure.infinitePi (fun _ : Fin k => stepFieldLaw μ)
  let C := fun roots => abstractMultiRootSelectionCell chosen A roots
  let D := fun roots =>
    C roots ∩ multiRootSubtreeStepFieldVector roots ⁻¹' B
  have hCmeas (roots : Fin k → Fin m × 𝕍) :
      MeasurableSet (C roots) :=
    (multiRootStepFiltration (m := m) (X := X) |>.le n) _
      (abstractMultiRootSelectionCell_measurable chosen hchosen A hA roots)
  have hDmeas (roots : Fin k → Fin m × 𝕍) :
      MeasurableSet (D roots) :=
    (hCmeas roots).inter
      ((multiRootSubtreeStepFieldVector_measurable roots) hB)
  have hCpair : Pairwise (fun r s => Disjoint (C r) (C s)) := by
    intro r s hrs
    apply Set.disjoint_left.mpr
    intro step hcr hcs
    exact hrs (hcr.2.symm.trans hcs.2)
  have hDpair : Pairwise (fun r s => Disjoint (D r) (D s)) := by
    intro r s hrs
    exact (hCpair hrs).mono Set.inter_subset_left Set.inter_subset_left
  have hCunion : (⋃ roots, C roots) = A := by
    ext step
    simp only [Set.mem_iUnion, C, abstractMultiRootSelectionCell,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨roots, hAstep, _⟩
      exact hAstep
    · intro hAstep
      exact ⟨chosen step, hAstep, rfl⟩
  have hDunion : (⋃ roots, D roots) =
      A ∩ selectedMultiRootSubtreeStepFieldVector chosen ⁻¹' B := by
    ext step
    simp only [Set.mem_iUnion, D, C, abstractMultiRootSelectionCell,
      Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      selectedMultiRootSubtreeStepFieldVector]
    constructor
    · rintro ⟨roots, ⟨⟨hAstep, hchoose⟩, hBstep⟩⟩
      exact ⟨hAstep, by simpa [hchoose] using hBstep⟩
    · rintro ⟨hAstep, hBstep⟩
      exact ⟨chosen step, ⟨⟨hAstep, rfl⟩, hBstep⟩⟩
  have hCsum : (∑' roots, P (C roots)) = P A := by
    rw [← hCunion]
    exact (measure_iUnion hCpair hCmeas).symm
  calc
    P (A ∩ selectedMultiRootSubtreeStepFieldVector chosen ⁻¹' B) =
        P (⋃ roots, D roots) := by rw [hDunion]
    _ = ∑' roots, P (D roots) := measure_iUnion hDpair hDmeas
    _ = ∑' roots, P (C roots) * Q B := by
      apply tsum_congr
      intro roots
      exact abstractMultiRootSelectionCell_factorization μ chosen hchosen
        hdepth hinj A B hA hB roots
    _ = (∑' roots, P (C roots)) * Q B := ENNReal.tsum_mul_right
    _ = P A * Q B := by rw [hCsum]

end ProbabilityTheory.BranchingRandomWalk

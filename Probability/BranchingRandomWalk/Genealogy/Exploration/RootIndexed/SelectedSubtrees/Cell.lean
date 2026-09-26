import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Vector

/-!
# Selection cells at a fixed generation

A selection cell fixes both the past event and the chosen root vector. On each
cell the descendant fields have the product law of fresh independent fields.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


def abstractMultiRootSelectionCell
    {m k : ℕ} {X : Type*}
    (chosen : FiniteRootStepField m X → Fin k → Fin m × 𝕍)
    (A : Set (FiniteRootStepField m X))
    (roots : Fin k → Fin m × 𝕍) :
    Set (FiniteRootStepField m X) :=
  A ∩ {step | chosen step = roots}

theorem abstractMultiRootSelectionCell_measurable
    {m k n : ℕ} {X : Type*} [MeasurableSpace X]
    (chosen : FiniteRootStepField m X → Fin k → Fin m × 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen)
    (A : Set (FiniteRootStepField m X))
    (hA : MeasurableSet[
      multiRootStepFiltration (m := m) (X := X) n] A)
    (roots : Fin k → Fin m × 𝕍) :
    MeasurableSet[multiRootStepFiltration (m := m) (X := X) n]
      (abstractMultiRootSelectionCell chosen A roots) :=
  hA.inter (hchosen (measurableSet_singleton roots))

theorem abstractMultiRootSelectionCell_factorization
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
    (hB : MeasurableSet B)
    (roots : Fin k → Fin m × 𝕍) :
    finiteRootStepFieldLaw μ m
        (abstractMultiRootSelectionCell chosen A roots ∩
          multiRootSubtreeStepFieldVector roots ⁻¹' B) =
      finiteRootStepFieldLaw μ m
          (abstractMultiRootSelectionCell chosen A roots) *
        (Measure.infinitePi (fun _ : Fin k => stepFieldLaw μ)) B := by
  by_cases hr : ∃ step, chosen step = roots
  · obtain ⟨step, hs⟩ := hr
    have hlen : ∀ j, (roots j).2.length = n := by
      intro j
      simpa [← hs] using hdepth step j
    have hroots_inj : Function.Injective roots := by
      simpa [← hs] using hinj step
    exact fixed_multiRootSubtreeStepFieldVector_event_factorization μ roots
      hlen hroots_inj _ _
      (abstractMultiRootSelectionCell_measurable chosen hchosen A hA roots) hB
  · have hempty : abstractMultiRootSelectionCell chosen A roots = ∅ := by
      ext step
      simp only [abstractMultiRootSelectionCell, Set.mem_inter_iff,
        Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, hs⟩
      exact hr ⟨step, hs⟩
    simp [hempty]

end ProbabilityTheory.BranchingRandomWalk

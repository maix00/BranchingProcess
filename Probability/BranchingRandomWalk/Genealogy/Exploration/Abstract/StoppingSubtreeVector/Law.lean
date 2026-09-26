import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppingSubtreeVector.Factorization

/-!
# Law and independence of the stopped subtree vector

The stopped subtree vector is measurable, its law is the product of independent
copies of the original field, and it is independent of the stopping-time
σ-algebra.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


theorem selectedSubtreeStepFieldVector_measurable_of_measurable
    {X : Type*} [MeasurableSpace X] {k : ℕ}
    (roots : (𝕍 → Step ℕ X) → Fin k → 𝕍)
    (hroots : Measurable roots) :
    Measurable (selectedSubtreeStepFieldVector roots) := by
  have hjoint : Measurable
      (fun p : (Fin k → 𝕍) × (𝕍 → Step ℕ X) =>
        subtreeStepFieldVector p.1 p.2) :=
    measurable_from_prod_countable_right subtreeStepFieldVector_measurable
  exact hjoint.comp (hroots.prodMk measurable_id)

theorem stopped_selectedSubtreeStepFieldVector_law
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    {k : ℕ}
    (τ : (𝕍 → Step ℕ X) → WithTop ℕ)
    (hτ : IsStoppingTime
      (generationFiltration (M := Step ℕ X)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (roots : (𝕍 → Step ℕ X) → Fin k → 𝕍)
    (hroots : Measurable[hτ.measurableSpace] roots)
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) →
      ∀ i, (roots ω i).length = n)
    (hinj : ∀ ω, Function.Injective (roots ω)) :
    (stepFieldLaw μ).map
        (selectedSubtreeStepFieldVector roots) =
      Measure.infinitePi (fun _ : Fin k => stepFieldLaw μ) := by
  have hrootsFull : Measurable roots :=
    hroots.mono hτ.measurableSpace_le le_rfl
  ext B hB
  rw [Measure.map_apply
    (selectedSubtreeStepFieldVector_measurable_of_measurable roots hrootsFull)
    hB]
  have hfactor := stopped_selectedSubtreeStepFieldVector_event_factorization μ
    τ hτ hfinite roots hroots hdepth hinj Set.univ B (by simp) hB
  simpa using hfactor

theorem stopped_selectedSubtreeStepFieldVector_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    {k : ℕ}
    (τ : (𝕍 → Step ℕ X) → WithTop ℕ)
    (hτ : IsStoppingTime
      (generationFiltration (M := Step ℕ X)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (roots : (𝕍 → Step ℕ X) → Fin k → 𝕍)
    (hroots : Measurable[hτ.measurableSpace] roots)
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) →
      ∀ i, (roots ω i).length = n)
    (hinj : ∀ ω, Function.Injective (roots ω)) :
    Indep hτ.measurableSpace
      (MeasurableSpace.comap
        (selectedSubtreeStepFieldVector roots) inferInstance)
      (stepFieldLaw μ) := by
  have hrootsFull : Measurable roots :=
    hroots.mono hτ.measurableSpace_le le_rfl
  have hselected :=
    selectedSubtreeStepFieldVector_measurable_of_measurable roots hrootsFull
  apply (indep_iff_forall_indepSet (stepFieldLaw μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  apply (indepSet_iff_measure_inter_eq_mul
    (hτ.measurableSpace_le _ hA) (hselected hB)
    (stepFieldLaw μ)).2
  have hlaw : stepFieldLaw μ
      (selectedSubtreeStepFieldVector roots ⁻¹' B) =
      (Measure.infinitePi (fun _ : Fin k => stepFieldLaw μ)) B := by
    rw [← Measure.map_apply hselected hB,
      stopped_selectedSubtreeStepFieldVector_law μ τ hτ hfinite roots
        hroots hdepth hinj]
  rw [hlaw]
  exact stopped_selectedSubtreeStepFieldVector_event_factorization μ τ hτ
    hfinite roots hroots hdepth hinj A B hA hB

end ProbabilityTheory.BranchingRandomWalk

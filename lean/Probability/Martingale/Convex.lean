import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Probability.Martingale.Basic

/-!
# Convex functions of martingales

This file supplies the standard conditional-Jensen bridge from martingales to
submartingales.  It is independent of branching and random walks, and belongs
to the common probability layer.
-/

open MeasureTheory

namespace MeasureTheory

variable {ι Ω E : Type*} [PartialOrder ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ι → Ω → E}
  {ℱ : Filtration ι mΩ} [SigmaFiniteFiltration μ ℱ]

/-- A continuous convex real-valued function of a martingale is a
submartingale, provided the transformed coordinates are integrable. -/
theorem Martingale.submartingale_convex_comp (hX : Martingale X ℱ μ)
    {φ : E → ℝ} (hφconvex : ConvexOn ℝ Set.univ φ)
    (hφcontinuous : Continuous φ)
    (hφintegrable : ∀ n, Integrable (fun ω => φ (X n ω)) μ) :
    Submartingale (fun n ω => φ (X n ω)) ℱ μ := by
  refine ⟨fun i => hφcontinuous.comp_stronglyMeasurable
      (hX.stronglyAdapted i), fun i j hij => ?_, hφintegrable⟩
  calc
    (fun ω => φ (X i ω)) =ᵐ[μ]
        fun ω => φ (μ[X j | ℱ i] ω) :=
      (hX.condExp_ae_eq hij).fun_comp φ |>.symm
    _ ≤ᵐ[μ] μ[fun ω => φ (X j ω) | ℱ i] :=
      hφconvex.map_condExp_le_univ (ℱ.le i)
        hφcontinuous.lowerSemicontinuous (hX.integrable j)
        (hφintegrable j)

end MeasureTheory

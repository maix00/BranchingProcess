import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Unit-time intensity of marked jumps

Lebesgue time on the unit interval has total mass one. Thus a product jump
intensity has the same mark integral and full-time mark masses as its mark
measure. These identities connect one-dimensional Lévy-measure estimates to
the Poisson path model.
-/

namespace ProbabilityTheory

open MeasureTheory

/-- A mark-only nonnegative integral is unchanged by adjoining unit-time
Lebesgue intensity. -/
theorem lintegral_unitTime_prod_mark
    (ν : Measure ℝ) [SigmaFinite ν]
    (f : ℝ → ENNReal) (hf : Measurable f) :
    (∫⁻ z : unitInterval × ℝ, f z.2
      ∂((volume : Measure unitInterval).prod ν)) =
      ∫⁻ x, f x ∂ν := by
  rw [lintegral_prod (fun z : unitInterval × ℝ => f z.2)
    (hf.comp measurable_snd).aemeasurable]
  simp

/-- A Bochner-integrable mark observable is likewise unchanged by the
unit-time product intensity. -/
theorem integral_unitTime_prod_mark
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν : Measure ℝ) [SigmaFinite ν]
    (f : ℝ → E) (hf : Integrable f ν) :
    (∫ z : unitInterval × ℝ, f z.2
      ∂((volume : Measure unitInterval).prod ν)) =
      ∫ x, f x ∂ν := by
  rw [integral_prod _ (hf.comp_snd (volume : Measure unitInterval))]
  simp

/-- The product intensity of a full-time mark window equals its Lévy mark
mass, including infinite mass. -/
theorem unitTime_prod_markWindow
    (ν : Measure ℝ) [SigmaFinite ν] (A : Set ℝ) :
    ((volume : Measure unitInterval).prod ν) (Set.univ ×ˢ A) = ν A := by
  rw [Measure.prod_prod]
  simp

/-- Restricting mark intensity to a region does not change the mass of a
measurable window already inside that region. -/
theorem unitTime_prod_restrict_markWindow
    (ν : Measure ℝ) [SigmaFinite ν]
    {A J : Set ℝ} (hJ : MeasurableSet J) (hJA : J ⊆ A) :
    ((volume : Measure unitInterval).prod (ν.restrict A))
      (Set.univ ×ˢ J) = ν J := by
  rw [unitTime_prod_markWindow, Measure.restrict_apply hJ]
  congr 1
  exact Set.inter_eq_left.mpr hJA

end ProbabilityTheory

module

public import Probability.Process.Stable.SmallDeviation.Blocks.ReturnScale

/-!
# The stable short entrance block

At duration `a ^ α`, a corridor and endpoint window scaled by `a` have the
same probability as the unscaled unit-time event. This is the scaling step
in the entrance factor of the shifted-corridor comparison.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The short entrance time corresponding to spatial scale `a`. -/
noncomputable def stableEntranceHorizon (α a : ℝ) : ℝ≥0 :=
  Real.toNNReal (a ^ α)

theorem IsStableLevyProcess.shortEntrance_corridorReturn_probability
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (a : ℝ) (ha : 0 < a)
    (lower upper coreLower coreUpper : ℝ) :
    P ((fun ω q => X ((stableEntranceHorizon α a) *
        rationalUnitTime q) ω - X 0 ω) ⁻¹'
      rationalCoordinateCorridorReturn
        (a * lower) (a * upper) (a * coreLower) (a * coreUpper)) =
    P ((fun ω q => X (rationalUnitTime q) ω - X 0 ω) ⁻¹'
      rationalCoordinateCorridorReturn lower upper coreLower coreUpper) := by
  let horizon : ℝ≥0 := stableEntranceHorizon α a
  have hhorizon : 0 < horizon := by
    apply NNReal.coe_pos.mp
    simp [horizon, stableEntranceHorizon,
      Real.coe_toNNReal _ (Real.rpow_pos_of_pos ha α).le]
    exact Real.rpow_pos_of_pos ha α
  have hα : 0 < α := h.increments.strictlyStable.1
  have hscale : (horizon : ℝ) ^ (-(1 / α)) = a⁻¹ := by
    rw [show (horizon : ℝ) = a ^ α by
      simp [horizon, stableEntranceHorizon,
        Real.coe_toNNReal _ (Real.rpow_pos_of_pos ha α).le]]
    rw [← Real.rpow_mul ha.le]
    have hexp : α * (-(1 / α)) = -1 := by
      field_simp
    rw [hexp, Real.rpow_neg_one]
  have hs := h.corridorReturn_timeSpaceScale_inv horizon hhorizon
    (a * lower) (a * upper) (a * coreLower) (a * coreUpper)
  simp only [hscale] at hs
  have ha0 : a ≠ 0 := ha.ne'
  have hcancel (x : ℝ) : a * x * a⁻¹ = x := by
    field_simp
  rw [hcancel lower, hcancel upper, hcancel coreLower, hcancel coreUpper] at hs
  simpa [horizon] using hs

/-- A positive unit-time corridor-and-endpoint probability gives the same
positive lower bound at every spatial scale. -/
theorem IsStableLevyProcess.shortEntrance_corridorReturn_pos
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (lower upper coreLower coreUpper : ℝ)
    (hpositive : 0 < P ((fun ω q => X (rationalUnitTime q) ω - X 0 ω) ⁻¹'
      rationalCoordinateCorridorReturn lower upper coreLower coreUpper))
    (a : ℝ) (ha : 0 < a) :
    0 < P ((fun ω q => X (stableEntranceHorizon α a *
        rationalUnitTime q) ω - X 0 ω) ⁻¹'
      rationalCoordinateCorridorReturn
        (a * lower) (a * upper) (a * coreLower) (a * coreUpper)) := by
  rw [h.shortEntrance_corridorReturn_probability a ha]
  exact hpositive

end ProbabilityTheory

end

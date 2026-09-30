module

public import Probability.Process.Stable.SmallDeviation.Blocks.Independence
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Gluing

/-!
# A fixed entrance block and its independent continuation

The complete rational-coordinate increment paths on adjacent intervals are
independent. Hence a corridor-and-endpoint event on the first interval and a
translated corridor event on the second have product probability.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The first block and the following translated block are independent as
random paths, for arbitrary nonnegative block lengths. -/
theorem IsStableLevyProcess.indepFun_entranceAndContinuation
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (cut remaining : ℝ≥0) :
    (fun ω q => X (cut * rationalUnitTime q) ω - X 0 ω) ⟂ᵢ[P]
    (fun ω q => X (cut + remaining * rationalUnitTime q) ω - X cut ω) := by
  apply h.increments.indepIncrements.indepFun_adjacentPaths
    (fun t => h.increments.aemeasurable_eval t)
    0 cut (cut + remaining)
    (fun q => cut * rationalUnitTime q)
    (fun q => cut + remaining * rationalUnitTime q)
  · intro q
    constructor
    · exact bot_le
    · simpa using mul_le_mul_of_nonneg_left (rationalUnitTime_le_one q)
        cut.property
  · intro q
    constructor
    · exact le_add_of_nonneg_right (by positivity)
    · simpa using add_le_add_left
        (mul_le_mul_of_nonneg_left (rationalUnitTime_le_one q)
          remaining.property) cut

/-- The probability of an endpoint-constrained entrance block and an
independent translated continuation is exactly the product of their
probabilities. -/
theorem IsStableLevyProcess.measure_entrance_inter_continuation
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (cut remaining : ℝ≥0)
    (lower upper coreLower coreUpper nextLower nextUpper : ℝ) :
    P (((fun ω q => X (cut * rationalUnitTime q) ω - X 0 ω) ⁻¹'
        rationalCoordinateCorridorReturn lower upper coreLower coreUpper) ∩
      ((fun ω q => X (cut + remaining * rationalUnitTime q) ω - X cut ω) ⁻¹'
        rationalCoordinateCorridor nextLower nextUpper)) =
      P ((fun ω q => X (cut * rationalUnitTime q) ω - X 0 ω) ⁻¹'
        rationalCoordinateCorridorReturn lower upper coreLower coreUpper) *
      P ((fun ω q => X (cut + remaining * rationalUnitTime q) ω - X cut ω) ⁻¹'
        rationalCoordinateCorridor nextLower nextUpper) := by
  exact (h.indepFun_entranceAndContinuation cut remaining).measure_inter_preimage_eq_mul
    _ _ (measurableSet_rationalCoordinateCorridorReturn
      lower upper coreLower coreUpper)
      (measurableSet_rationalCoordinateCorridor nextLower nextUpper)

end ProbabilityTheory

end

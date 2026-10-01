module

public import Probability.Process.Stable.SmallDeviation.Blocks.Independence
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Gluing
public import Probability.Process.Path.Skorokhod.Corridor.Segment
public import Probability.Process.Stable.SmallDeviation.Blocks.Stationarity

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

/-- The fixed-cut product identity for complete càdlàg corridor events.
Countable coordinates occur only inside the measurability and independence
proof; the event in the statement constrains every time in each segment. -/
theorem IsStableLevyProcess.measure_fullEntrance_inter_continuation
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (cut remaining : ℝ≥0)
    (lower upper coreLower coreUpper nextLower nextUpper : ℝ) :
    P (fullSegmentCorridorReturnEvent X 0 cut
        lower upper coreLower coreUpper ∩
      fullSegmentCorridorEvent X cut remaining nextLower nextUpper) =
      P (fullSegmentCorridorReturnEvent X 0 cut
        lower upper coreLower coreUpper) *
      P (fullSegmentCorridorEvent X cut remaining nextLower nextUpper) := by
  let A : Set Ω :=
    (fun ω q => X (cut * rationalUnitTime q) ω - X 0 ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorReturnWithMargin
        lower upper coreLower coreUpper
  let B : Set Ω :=
    (fun ω q => X (cut + remaining * rationalUnitTime q) ω - X cut ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorWithMargin nextLower nextUpper
  have hprod : P (A ∩ B) = P A * P B := by
    exact (h.indepFun_entranceAndContinuation cut remaining).measure_inter_preimage_eq_mul
      _ _ (Skorokhod.measurableSet_rationalCoordinateCorridorReturnWithMargin
        lower upper coreLower coreUpper)
        (Skorokhod.measurableSet_rationalCoordinateCorridorWithMargin
          nextLower nextUpper)
  have haeA : A =ᵐ[P] fullSegmentCorridorReturnEvent X 0 cut
      lower upper coreLower coreUpper := by
    filter_upwards [h.ae_cadlag] with ω hω
    have hiff := mem_fullSegmentCorridorReturnEvent_iff_rational
      X 0 cut lower upper coreLower coreUpper ω hω
    simpa [A, zero_add] using propext hiff.symm
  have haeB : B =ᵐ[P]
      fullSegmentCorridorEvent X cut remaining nextLower nextUpper := by
    filter_upwards [h.ae_cadlag] with ω hω
    exact propext (mem_fullSegmentCorridorEvent_iff_rational
      X cut remaining nextLower nextUpper ω hω).symm
  have haeInter : A ∩ B =ᵐ[P]
      fullSegmentCorridorReturnEvent X 0 cut
        lower upper coreLower coreUpper ∩
      fullSegmentCorridorEvent X cut remaining nextLower nextUpper := by
    filter_upwards [haeA, haeB] with ω hA hB
    simp [hA, hB]
  rw [measure_congr haeInter, measure_congr haeA, measure_congr haeB] at hprod
  exact hprod

/-- Adjacent complete-path corridor events with endpoint windows have
product probability. -/
theorem IsStableLevyProcess.measure_fullReturn_inter_return
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (cut remaining : ℝ≥0)
    (lower upper firstLower firstUpper nextLower nextUpper
      secondLower secondUpper : ℝ) :
    P (fullSegmentCorridorReturnEvent X 0 cut
        lower upper firstLower firstUpper ∩
      fullSegmentCorridorReturnEvent X cut remaining
        nextLower nextUpper secondLower secondUpper) =
      P (fullSegmentCorridorReturnEvent X 0 cut
        lower upper firstLower firstUpper) *
      P (fullSegmentCorridorReturnEvent X cut remaining
        nextLower nextUpper secondLower secondUpper) := by
  let A : Set Ω :=
    (fun ω q => X (cut * rationalUnitTime q) ω - X 0 ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorReturnWithMargin
        lower upper firstLower firstUpper
  let B : Set Ω :=
    (fun ω q => X (cut + remaining * rationalUnitTime q) ω - X cut ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorReturnWithMargin
        nextLower nextUpper secondLower secondUpper
  have hprod : P (A ∩ B) = P A * P B := by
    exact (h.indepFun_entranceAndContinuation cut remaining).measure_inter_preimage_eq_mul
      _ _ (Skorokhod.measurableSet_rationalCoordinateCorridorReturnWithMargin
        lower upper firstLower firstUpper)
        (Skorokhod.measurableSet_rationalCoordinateCorridorReturnWithMargin
          nextLower nextUpper secondLower secondUpper)
  have haeA : A =ᵐ[P] fullSegmentCorridorReturnEvent X 0 cut
      lower upper firstLower firstUpper := by
    filter_upwards [h.ae_cadlag] with ω hω
    have hiff := mem_fullSegmentCorridorReturnEvent_iff_rational
      X 0 cut lower upper firstLower firstUpper ω hω
    simpa [A, zero_add] using propext hiff.symm
  have haeB : B =ᵐ[P] fullSegmentCorridorReturnEvent X cut remaining
      nextLower nextUpper secondLower secondUpper := by
    filter_upwards [h.ae_cadlag] with ω hω
    exact propext (mem_fullSegmentCorridorReturnEvent_iff_rational
      X cut remaining nextLower nextUpper secondLower secondUpper ω hω).symm
  have haeInter : A ∩ B =ᵐ[P]
      fullSegmentCorridorReturnEvent X 0 cut
        lower upper firstLower firstUpper ∩
      fullSegmentCorridorReturnEvent X cut remaining
        nextLower nextUpper secondLower secondUpper := by
    filter_upwards [haeA, haeB] with ω hA hB
    simp [hA, hB]
  rw [measure_congr haeInter, measure_congr haeA, measure_congr haeB] at hprod
  exact hprod

/-- A two-block lower bound retaining both the corridor and final endpoint
window. -/
theorem IsStableLevyProcess.measure_fullReturn_ge_return_mul_return
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (cut remaining : ℝ≥0) (hcut : 0 < cut) (hremaining : 0 < remaining)
    (lower upper firstLower firstUpper secondLower secondUpper : ℝ) :
    P (fullSegmentCorridorReturnEvent X 0 cut
        lower upper firstLower firstUpper) *
      P (fullSegmentCorridorReturnEvent X cut remaining
        (lower - firstLower) (upper - firstUpper)
        secondLower secondUpper) ≤
      P (fullSegmentCorridorReturnEvent X 0 (cut + remaining)
        lower upper (firstLower + secondLower) (firstUpper + secondUpper)) := by
  rw [← h.measure_fullReturn_inter_return cut remaining]
  exact measure_mono (fullReturn_inter_return_subset_fullReturn X
    cut remaining hcut hremaining lower upper firstLower firstUpper
    secondLower secondUpper)

/-- The fixed-cut lower bound for the full path corridor. The first factor
requires an endpoint window; the second is a translated corridor for the
continuation. -/
theorem IsStableLevyProcess.measure_fullCorridor_ge_entrance_mul_continuation
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (cut remaining : ℝ≥0) (hcut : 0 < cut) (hremaining : 0 < remaining)
    (lower upper endpointLower endpointUpper : ℝ) :
    P (fullSegmentCorridorReturnEvent X 0 cut
        lower upper endpointLower endpointUpper) *
      P (fullSegmentCorridorEvent X cut remaining
        (lower - endpointLower) (upper - endpointUpper)) ≤
      P (fullSegmentCorridorEvent X 0 (cut + remaining) lower upper) := by
  rw [← h.measure_fullEntrance_inter_continuation cut remaining]
  exact measure_mono
    (fullEntrance_inter_continuation_subset_fullCorridor X cut remaining
      hcut hremaining lower upper endpointLower endpointUpper)

/-- The complete-path form of the first inequality in Mogulskii's proof of
the interval comparison: after entering a smaller endpoint window, the
continuation is compared with a corridor over the whole horizon. -/
theorem IsStableLevyProcess.measure_fullCorridor_ge_entrance_mul_fullCorridor
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (cut remaining : ℝ≥0) (hcut : 0 < cut) (hremaining : 0 < remaining)
    (lower upper endpointLower endpointUpper : ℝ) :
    P (fullSegmentCorridorReturnEvent X 0 cut
        lower upper endpointLower endpointUpper) *
      P (fullSegmentCorridorEvent X 0 (cut + remaining)
        (lower - endpointLower) (upper - endpointUpper)) ≤
      P (fullSegmentCorridorEvent X 0 (cut + remaining) lower upper) := by
  have hshort := h.measure_fullCorridor_ge_entrance_mul_continuation
    cut remaining hcut hremaining lower upper endpointLower endpointUpper
  rw [← h.measure_fullSegmentCorridor_shift cut remaining
    (lower - endpointLower) (upper - endpointUpper)] at hshort
  have hmono :
      P (fullSegmentCorridorEvent X 0 (cut + remaining)
        (lower - endpointLower) (upper - endpointUpper)) ≤
      P (fullSegmentCorridorEvent X 0 remaining
        (lower - endpointLower) (upper - endpointUpper)) := by
    apply measure_mono
    exact fullSegmentCorridorEvent_mono_length X 0 remaining
      (cut + remaining) (by positivity) (by exact le_add_of_nonneg_left cut.property)
      (lower - endpointLower) (upper - endpointUpper)
  calc
    _ ≤ P (fullSegmentCorridorReturnEvent X 0 cut
          lower upper endpointLower endpointUpper) *
        P (fullSegmentCorridorEvent X 0 remaining
          (lower - endpointLower) (upper - endpointUpper)) := by gcongr
    _ ≤ _ := hshort

end ProbabilityTheory

end

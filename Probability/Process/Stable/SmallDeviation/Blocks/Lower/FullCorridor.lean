module

public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.TwoBins
public import Probability.Process.Path.Skorokhod.Corridor.Enlargement
public import Probability.Distributions.Stable.Sign

/-!
# Positive complete-path corridors for stable processes

The finite two-bin return construction yields a positive range tube. A
smaller range tube forces the centered complete path into any corridor that
contains zero. The CDF hypothesis is the one used in Mogulskii's lemma.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem IsStableLevyProcess.measure_fullSegmentCorridor_pos
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (lower upper : ℝ) (hlower : lower < 0) (hupper : 0 < upper)
    (hpos : 0 < μ (Set.Ioi 0)) (hneg : 0 < μ (Set.Iio 0)) :
    0 < P (fullSegmentCorridorEvent X 0 1 lower upper) := by
  let width : ℝ := min (-lower) upper / 2
  have hwidth : 0 < width := by
    dsimp [width]
    exact half_pos (lt_min (by linarith) hupper)
  have hwidthLower : lower < -width := by
    dsimp [width]
    have hmin := min_le_left (-lower) upper
    linarith
  have hwidthUpper : width < upper := by
    dsimp [width]
    have hmin := min_le_right (-lower) upper
    linarith
  have htube := h.measure_rationalHorizonTube_pos
    width hwidth hpos hneg
  exact htube.trans_le
    (measure_rationalHorizonTube_le_fullSegmentCorridor
      P X 1 lower upper width hwidth hwidthLower hwidthUpper h.ae_cadlag)

/-- The original CDF condition supplies the two sign masses used by the
abstract complete-corridor positivity theorem. -/
theorem IsStableLevyProcess.measure_fullSegmentCorridor_pos_of_cdfAtZero
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P] [NullSingletonClass μ]
    (h : IsStableLevyProcess α μ X P)
    (lower upper : ℝ) (hlower : lower < 0) (hupper : 0 < upper)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    0 < P (fullSegmentCorridorEvent X 0 1 lower upper) := by
  obtain ⟨hneg, hpos⟩ :=
    h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
  exact h.measure_fullSegmentCorridor_pos
    lower upper hlower hupper hpos hneg

end ProbabilityTheory

end

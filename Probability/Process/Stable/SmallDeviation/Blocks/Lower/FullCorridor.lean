module

public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.TwoBins
public import Probability.Process.Path.Skorokhod.Corridor.Enlargement
public import Probability.Distributions.Stable.Sign
public import Probability.Process.Path.Skorokhod.Corridor.Support

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

/-- The complete centered-corridor estimates place the zero path in the
support of a measurable càdlàg representative of the unit segment. -/
theorem IsStableLevyProcess.straightPath_zero_mem_segmentLaw_support
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (F : Ω → CadlagPath unitInterval ℝ) (hF : Measurable F)
    (hpath : ∀ᵐ ω ∂P, ∀ t : unitInterval,
      F ω t = segmentIncrement X 0 1 ω t)
    (hpos : 0 < μ (Set.Ioi 0)) (hneg : 0 < μ (Set.Iio 0)) :
    Skorokhod.straightPath 0 ∈ (P.map F).support := by
  apply straightPath_zero_mem_support_of_centeredCorridors_pos
  intro δ hδ
  have hcorridor : 0 < P (fullSegmentCorridorEvent X 0 1 (-δ) δ) :=
    h.measure_fullSegmentCorridor_pos (-δ) δ (by linarith) hδ hpos hneg
  have heq : F ⁻¹' Skorokhod.rangeInOpenInterval (-δ) δ =ᵐ[P]
      fullSegmentCorridorEvent X 0 1 (-δ) δ := by
    filter_upwards [hpath] with ω hω
    apply propext
    simp only [Set.mem_preimage, Skorokhod.rangeInOpenInterval,
      fullSegmentCorridorEvent, Set.mem_setOf_eq]
    constructor
    · rintro ⟨margin, hmargin, hbound⟩
      exact ⟨margin, hmargin, fun t => by simpa [hω t] using hbound t⟩
    · rintro ⟨margin, hmargin, hbound⟩
      exact ⟨margin, hmargin, fun t => by simpa [hω t] using hbound t⟩
  rw [Measure.map_apply hF
    (Skorokhod.measurableSet_rangeInOpenInterval (-δ) δ), measure_congr heq]
  exact hcorridor

/-- The original CDF condition supplies the two sign masses used by the
abstract complete-corridor positivity theorem. -/
theorem IsStableLevyProcess.measure_fullSegmentCorridor_pos_of_cdfAtZero
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (lower upper : ℝ) (hlower : lower < 0) (hupper : 0 < upper)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    0 < P (fullSegmentCorridorEvent X 0 1 lower upper) := by
  obtain ⟨hneg, hpos⟩ :=
    h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
  exact h.measure_fullSegmentCorridor_pos
    lower upper hlower hupper hpos hneg

/-- If both the path corridor and endpoint window contain zero, two-sided
increment mass makes the complete entrance event positive. -/
theorem IsStableLevyProcess.measure_fullSegmentCorridorReturn_pos_of_zero_mem
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (lower upper coreLower coreUpper : ℝ)
    (hlower : lower < 0) (hupper : 0 < upper)
    (hcoreLower : coreLower < 0) (hcoreUpper : 0 < coreUpper)
    (hpos : 0 < μ (Set.Ioi 0)) (hneg : 0 < μ (Set.Iio 0)) :
    0 < P (fullSegmentCorridorReturnEvent X 0 1
      lower upper coreLower coreUpper) := by
  let width : ℝ :=
    min (min (-lower) upper) (min (-coreLower) coreUpper) / 2
  have hwidth : 0 < width := by
    dsimp [width]
    apply half_pos
    exact lt_min (lt_min (by linarith) hupper)
      (lt_min (by linarith) hcoreUpper)
  have hwidthLower : width < -lower := by
    dsimp [width]
    have hmin := (min_le_left
      (min (-lower) upper) (min (-coreLower) coreUpper)).trans
      (min_le_left (-lower) upper)
    linarith
  have hwidthUpper : width < upper := by
    dsimp [width]
    have hmin := (min_le_left
      (min (-lower) upper) (min (-coreLower) coreUpper)).trans
      (min_le_right (-lower) upper)
    linarith
  have hwidthCoreLower : width < -coreLower := by
    dsimp [width]
    have hmin := (min_le_right
      (min (-lower) upper) (min (-coreLower) coreUpper)).trans
      (min_le_left (-coreLower) coreUpper)
    linarith
  have hwidthCoreUpper : width < coreUpper := by
    dsimp [width]
    have hmin := (min_le_right
      (min (-lower) upper) (min (-coreLower) coreUpper)).trans
      (min_le_right (-coreLower) coreUpper)
    linarith
  have hsmall : 0 < P (fullSegmentCorridorEvent X 0 1 (-width) width) :=
    h.measure_fullSegmentCorridor_pos (-width) width
      (by linarith) hwidth hpos hneg
  apply hsmall.trans_le
  apply measure_mono
  rintro ω ⟨margin, hmargin, hpath⟩
  refine ⟨⟨margin, hmargin, ?_⟩, ?_⟩
  · intro t
    have ht := hpath t
    constructor <;> linarith
  · have ht := hpath ⊤
    exact ⟨by linarith, by linarith⟩

end ProbabilityTheory

end

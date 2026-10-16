/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Probability.Process.Path.Skorokhod.Corridor.Segment
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Cover
public import Topology.Cadlag.Skorokhod.SmallDeviation.RangeCover
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Topology.Order.UnitInterval.Rational

/-!
# Range and corridor events for real-valued processes

The range event is expressed by rational coordinates on the original sample
space. Almost-sure càdlàg paths identify it with complete-segment corridor
events, so finite deterministic covers can be used without a path-space law.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal ENNReal

/-- Probability of the centered full-segment corridor with half-width `a`.
This path-event probability does not require any stable-process structure. -/
def centeredCorridorProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (a : ℝ) : ℝ≥0∞ :=
  P (fullSegmentCorridorEvent X 0 1 (-a) a)

/-- Probability that the full path range has diameter strictly less than
`2 * a`, expressed through rational coordinates of the original process. -/
def rationalRangeProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (a : ℝ) : ℝ≥0∞ :=
  P (rationalHorizonTubeEvent X 1 (2 * a))

/-- Probability of the centered full-segment corridor enlarged by the factor
`1 + ε`. -/
def expandedCenteredCorridorProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (ε a : ℝ) : ℝ≥0∞ :=
  P (fullSegmentCorridorEvent X 0 1 (-(1 + ε) * a) ((1 + ε) * a))

/-- Probability of the `j`th translated corridor in a finite range cover. -/
def rangeCoverCorridorProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (a : ℝ) (k j : ℕ) : ℝ≥0∞ :=
  P (fullSegmentCorridorEvent X 0 1
    (a * (((j : ℝ) / k - 1) - (1 + 2 / k)))
    (a * (((j : ℝ) / k - 1) + (1 + 2 / k))))

/-- A complete corridor with uniform margin is contained in the rational
range event of its exact total width. -/
theorem fullSegmentCorridorEvent_subset_rationalHorizonTubeEvent_exact
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (lower upper : ℝ) :
    fullSegmentCorridorEvent X 0 1 lower upper ⊆
      rationalHorizonTubeEvent X 1 (upper - lower) := by
  intro ω hω
  obtain ⟨margin, hmargin, hpath⟩ := hω
  obtain ⟨m, hmpos, hm⟩ := exists_rat_btwn (show (0 : ℝ) < 2 * margin by positivity)
  have hcoord : ∀ q : RationalCoordinate.UnitInterval,
      lower + margin ≤
        X (RationalCoordinate.toNNReal q) ω - X 0 ω ∧
      X (RationalCoordinate.toNNReal q) ω - X 0 ω ≤ upper - margin := by
    intro q
    have hq := hpath (RationalCoordinate.toUnitInterval q)
    change lower + margin ≤
        X (0 + 1 * UnitInterval.toNNReal (RationalCoordinate.toUnitInterval q)) ω - X 0 ω ∧
      X (0 + 1 * UnitInterval.toNNReal (RationalCoordinate.toUnitInterval q)) ω - X 0 ω ≤
        upper - margin at hq
    have htime : UnitInterval.toNNReal (RationalCoordinate.toUnitInterval q) =
        RationalCoordinate.toNNReal q := rfl
    rw [htime] at hq
    simpa only [zero_add, one_mul] using hq
  have hratio :
      (fun q => X (RationalCoordinate.toNNReal q) ω - X 0 ω) ∈
        Skorokhod.rationalCoordinateOscillationTube (upper - lower) := by
    refine ⟨m, hmpos, ?_⟩
    intro s t
    have hs := hcoord s
    have ht := hcoord t
    apply abs_le.mpr
    constructor <;> linarith [hm]
  have hraw := (Skorokhod.mem_rationalCoordinateOscillationTube_sub_const_iff
    (upper - lower) (X 0 ω)
    (fun q => X (RationalCoordinate.toNNReal q) ω)).mp hratio
  change rationalHorizonProcess X 1 ω ∈
    Skorokhod.rationalCoordinateOscillationTube (upper - lower)
  change (fun q => X (1 * RationalCoordinate.toNNReal q) ω) ∈
    Skorokhod.rationalCoordinateOscillationTube (upper - lower)
  simpa using hraw

/-- A rational range bound on a càdlàg path gives a complete corridor around
zero whose half-width is the range bound. -/
theorem mem_rationalHorizonTubeEvent_imp_fullSegmentCorridorEvent
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (width : ℝ) (ω : Ω)
    (hω : IsCadlag (fun t => X t ω))
    (htube : ω ∈ rationalHorizonTubeEvent X 1 width) :
    ω ∈ fullSegmentCorridorEvent X 0 1 (-width) width := by
  have hraw :
      (fun q => X (1 * RationalCoordinate.toNNReal q) ω) ∈
        Skorokhod.rationalCoordinateOscillationTube width := htube
  change (fun q => X (1 * RationalCoordinate.toNNReal q) ω) ∈
    Skorokhod.rationalCoordinateOscillationTube width at hraw
  have hraw' :
      (fun q => X (RationalCoordinate.toNNReal q) ω) ∈
        Skorokhod.rationalCoordinateOscillationTube width := by
    simpa only [one_mul] using hraw
  have hcentered := (Skorokhod.mem_rationalCoordinateOscillationTube_sub_const_iff
    width (X 0 ω) (fun q => X (RationalCoordinate.toNNReal q) ω)).mpr (by
      exact hraw')
  obtain ⟨margin, hmargin, hosc⟩ := hcentered
  have hcoord :
      (fun q => X (0 + 1 * RationalCoordinate.toNNReal q) ω - X 0 ω) ∈
        Skorokhod.rationalCoordinateCorridorWithMargin (-width) width := by
    refine ⟨margin, hmargin, ?_⟩
    intro q
    have hq := hosc q ⊥
    change |(X (RationalCoordinate.toNNReal q) ω - X 0 ω) -
      (X (RationalCoordinate.toNNReal ⊥) ω - X 0 ω)| ≤ width - margin at hq
    have hzero : X (RationalCoordinate.toNNReal ⊥) ω - X 0 ω = 0 := by
      simp [RationalCoordinate.toNNReal_bot]
    rw [hzero, sub_zero, abs_le] at hq
    change -width + margin ≤
        X (0 + 1 * UnitInterval.toNNReal (RationalCoordinate.toUnitInterval q)) ω - X 0 ω ∧
      X (0 + 1 * UnitInterval.toNNReal (RationalCoordinate.toUnitInterval q)) ω - X 0 ω ≤
        width - margin
    have htime : UnitInterval.toNNReal (RationalCoordinate.toUnitInterval q) =
        RationalCoordinate.toNNReal q := rfl
    rw [zero_add, one_mul, htime]
    exact ⟨by linarith [hq.1], hq.2⟩
  exact (mem_fullSegmentCorridorEvent_iff_rational
    X 0 1 (-width) width ω hω).mpr (by
      simpa [RationalCoordinate.toNNReal] using hcoord)

/-- A rational range tube is covered on each càdlàg sample by the scaled
finite family of complete-segment corridors. -/
theorem rationalHorizonTubeEvent_subset_iUnion_scaledFullSegmentCorridors
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (k : ℕ) (hk : 0 < k) (ω : Ω)
    (hω : IsCadlag (fun t => X t ω))
    (htube : ω ∈ rationalHorizonTubeEvent X 1 (2 * a)) :
    ω ∈ ⋃ j ∈ Finset.range (2 * k + 1),
      fullSegmentCorridorEvent X 0 1
        (a * (((j : ℝ) / k - 1) - (1 + 2 / k)))
        (a * (((j : ℝ) / k - 1) + (1 + 2 / k))) := by
  let path : CadlagPath unitInterval ℝ :=
    ⟨segmentIncrement X 0 1 ω, isCadlag_segmentIncrement X 0 1 ω hω⟩
  let normalized : CadlagPath unitInterval ℝ := Skorokhod.scalePath a⁻¹ path
  have hraw :
      (fun q => X (1 * RationalCoordinate.toNNReal q) ω) ∈
        Skorokhod.rationalCoordinateOscillationTube (2 * a) := htube
  change (fun q => X (1 * RationalCoordinate.toNNReal q) ω) ∈
    Skorokhod.rationalCoordinateOscillationTube (2 * a) at hraw
  have hraw' :
      (fun q => X (RationalCoordinate.toNNReal q) ω) ∈
        Skorokhod.rationalCoordinateOscillationTube (2 * a) := by
    simpa only [one_mul] using hraw
  have hcentered := (Skorokhod.mem_rationalCoordinateOscillationTube_sub_const_iff
    (2 * a) (X 0 ω) (fun q => X (RationalCoordinate.toNNReal q) ω)).mpr (by
      exact hraw')
  rw [Skorokhod.rationalCoordinateOscillationTube_eq_real] at hcentered
  have hscaled :
      (fun q => a⁻¹ * (X (RationalCoordinate.toNNReal q) ω - X 0 ω)) ∈
        Skorokhod.rationalCoordinateOscillationTubeReal 2 := by
    apply (Skorokhod.mem_rationalCoordinateOscillationTubeReal_smul_iff
      (inv_pos.mpr ha) _).2
    simpa [div_eq_mul_inv, ha.ne'] using hcentered
  have hnormalized :
      (fun q => normalized (RationalCoordinate.toUnitInterval q)) ∈
        Skorokhod.rationalCoordinateOscillationTubeReal 2 := by
    have heq : (fun q => normalized (RationalCoordinate.toUnitInterval q)) =
        (fun q => a⁻¹ * (X (RationalCoordinate.toNNReal q) ω - X 0 ω)) := by
      funext q
      change a⁻¹ * segmentIncrement X 0 1 ω (RationalCoordinate.toUnitInterval q) = _
      simp only [segmentIncrement, zero_add, one_mul]
      have htime : UnitInterval.toNNReal (RationalCoordinate.toUnitInterval q) =
          RationalCoordinate.toNNReal q := rfl
      rw [htime]
    rw [heq]
    exact hscaled
  have hnormalized' : normalized ∈ Skorokhod.rangeTubeStartingAtZero 1 := by
    have hrat :
        (fun q => normalized (RationalCoordinate.toUnitInterval q)) ∈
          Skorokhod.rationalCoordinateOscillationTube 2 := by
      rwa [Skorokhod.rationalCoordinateOscillationTube_eq_real]
    have hosc : normalized ∈ Skorokhod.oscillationInOpenTube 2 := by
      rw [← Skorokhod.rationalOscillationInOpenTube_eq 2]
      simpa [Skorokhod.rationalOscillationInOpenTube,
        Skorokhod.rationalCoordinateOscillationTube] using hrat
    refine ⟨?_, ?_⟩
    · have hbot : UnitInterval.toNNReal (⊥ : unitInterval) = 0 := by
        apply NNReal.coe_injective
        rfl
      simp [normalized, path, Skorokhod.scalePath, segmentIncrement, hbot]
    · simpa [Skorokhod.rangeTubeStartingAtZero] using hosc
  have hcover := Skorokhod.rangeTubeStartingAtZero_subset_iUnion_corridors k hk
    hnormalized'
  simp only [Set.mem_iUnion] at hcover ⊢
  obtain ⟨j, hj, hcorr⟩ := hcover
  refine ⟨j, hj, ?_⟩
  have hcorr' :
      normalized ∈ Skorokhod.corridorStartingAtZero
        (((j : ℝ) / k - 1) - (1 + 2 / k))
        (((j : ℝ) / k - 1) + (1 + 2 / k)) := hcorr
  change normalized ⊥ = 0 ∧ _ at hcorr'
  rcases hcorr' with ⟨_, margin, hmargin, hbounds⟩
  refine ⟨a * margin, mul_pos ha hmargin, ?_⟩
  intro t
  have ht := hbounds t
  have hnormEq : normalized t = a⁻¹ * segmentIncrement X 0 1 ω t := by
    rfl
  rw [hnormEq] at ht
  have hcancel (x : ℝ) : a * (a⁻¹ * x) = x := by
    field_simp [ha.ne']
  constructor
  · have hmul := mul_le_mul_of_nonneg_left ht.1 ha.le
    rw [hcancel] at hmul
    nlinarith
  · have hmul := mul_le_mul_of_nonneg_left ht.2 ha.le
    rw [hcancel] at hmul
    nlinarith

/-- The probability version of the finite corridor cover, on the original
sample space. It only assumes almost-sure càdlàg paths and does not use a
probability measure on path space. -/
theorem measure_rationalHorizonTube_le_sum_scaledFullSegmentCorridors
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (k : ℕ) (hk : 0 < k)
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω)) :
    P (rationalHorizonTubeEvent X 1 (2 * a)) ≤
      ∑ j ∈ Finset.range (2 * k + 1),
        P (fullSegmentCorridorEvent X 0 1
          (a * (((j : ℝ) / k - 1) - (1 + 2 / k)))
          (a * (((j : ℝ) / k - 1) + (1 + 2 / k)))) := by
  calc
    _ ≤ P (⋃ j ∈ Finset.range (2 * k + 1),
        fullSegmentCorridorEvent X 0 1
          (a * (((j : ℝ) / k - 1) - (1 + 2 / k)))
          (a * (((j : ℝ) / k - 1) + (1 + 2 / k)))) := by
      apply measure_mono_ae
      filter_upwards [hcadlag] with ω hω
      exact rationalHorizonTubeEvent_subset_iUnion_scaledFullSegmentCorridors
        X a ha k hk ω hω
    _ ≤ _ := measure_biUnion_finset_le _ _

end ProbabilityTheory

end

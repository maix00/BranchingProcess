/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Topology.Order.LeftRightLim
public import Probability.Process.Path.Skorokhod.Corridor.Segment
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Cover
public import Topology.Cadlag.Basic
public import Topology.Cadlag.Skorokhod.SmallDeviation.RangeCover
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Topology.Order.UnitInterval.Rational

/-!
# Range and corridor events for real-valued processes

The range event is expressed by rational coordinates on the original sample
space. Almost-sure càdlàg paths identify it with complete-segment corridor
events, so finite deterministic covers can be used without a path-space law.

## Public declarations

- `ProbabilityTheory.centeredCorridorProbability`,
  `ProbabilityTheory.rationalRangeProbability`,
  `ProbabilityTheory.expandedCenteredCorridorProbability`, and
  `ProbabilityTheory.rangeCoverCorridorProbability`: probabilities on the
  original sample space of the centered corridor, rational range, enlarged
  centered corridor, and an individual corridor in a finite range cover.
- `ProbabilityTheory.rationalRangeProbability_eq_of_rationalProcess_identDistrib`:
  the law of the rational-coordinate process determines the rational range
  probability.
- `ProbabilityTheory.ae_rationalInteriorOscillationLe_implies_rationalCoordinateOscillationLe`:
  an almost-sure càdlàg path with no jump at time one extends a closed
  oscillation bound from rational times strictly before one to all rational
  times in the unit interval.
- `ProbabilityTheory.fullSegmentCorridorEvent_subset_rationalHorizonTubeEvent_exact`:
  a corridor of width $u-l$ is contained in the rational range event of
  width $u-l$.
- `ProbabilityTheory.mem_rationalHorizonTubeEvent_imp_fullSegmentCorridorEvent`:
  on a càdlàg sample path, rational range at width $a$ implies the full
  centered corridor $[-a,a]$.
- `ProbabilityTheory.rationalHorizonTubeEvent_subset_iUnion_scaledFullSegmentCorridors`:
  for $a>0$ and $k>0$, the range event of width $2a$ is contained in the
  union of $2k+1$ complete corridors with scale $a$.
- `ProbabilityTheory.measure_rationalHorizonTube_le_sum_scaledFullSegmentCorridors`:
  under almost-sure càdlàg paths, the range-event probability is at most the
  sum of those $2k+1$ corridor probabilities.
-/

@[expose] public section

namespace ProbabilityTheory

open Filter MeasureTheory
open scoped NNReal ENNReal Topology

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

/-- The rational-coordinate process law determines the probability of its
rational range-tube event. This applies to any real-valued processes, without
increment, stationarity, or path-regularity assumptions. -/
theorem rationalRangeProbability_eq_of_rationalProcess_identDistrib
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {X : ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω' → ℝ}
    {P : Measure Ω} {Q : Measure Ω'}
    (h : IdentDistrib
      (fun ω (q : RationalCoordinate.UnitInterval) =>
        X (RationalCoordinate.toNNReal q) ω)
      (fun ω (q : RationalCoordinate.UnitInterval) =>
        Y (RationalCoordinate.toNNReal q) ω) P Q)
    (a : ℝ) :
    rationalRangeProbability P X a = rationalRangeProbability Q Y a := by
  have hprob := h.measure_mem_eq
    (Skorokhod.measurableSet_rationalCoordinateOscillationTube (2 * a))
  have hprob' : P (rationalHorizonTubeEvent X 1 (2 * a)) =
      Q (rationalHorizonTubeEvent Y 1 (2 * a)) := by
    change P ((fun ω q => X (1 * RationalCoordinate.toNNReal q) ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube (2 * a)) =
      Q ((fun ω q => Y (1 * RationalCoordinate.toNNReal q) ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube (2 * a))
    simpa only [one_mul] using hprob
  simpa [rationalRangeProbability] using hprob'

/-- On almost-surely càdlàg paths with no jump at time one, a closed
oscillation bound on rational times strictly before one extends to all
rational coordinates in the unit interval. -/
theorem ae_rationalInteriorOscillationLe_implies_rationalCoordinateOscillationLe
    {Ω : Type*} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun s => X s ω))
    (hnoJump : ∀ᵐ ω ∂P, (fun s => X s ω).leftLim 1 = X 1 ω)
    (width : ℝ) :
    ∀ᵐ ω ∂P,
      (∀ s t : RationalCoordinate.UnitInterval, s < ⊤ → t < ⊤ →
        |X (RationalCoordinate.toNNReal s) ω - X (RationalCoordinate.toNNReal t) ω| ≤ width) →
      ∀ s t : RationalCoordinate.UnitInterval,
        |X (RationalCoordinate.toNNReal s) ω - X (RationalCoordinate.toNNReal t) ω| ≤ width := by
  filter_upwards [hcadlag, hnoJump] with ω hω hωjump
  intro hinterior s t
  have htoMono : Monotone RationalCoordinate.toUnitInterval := by
    intro q r hqr
    change ((q : ℚ) : ℝ) ≤ ((r : ℚ) : ℝ)
    exact_mod_cast hqr
  have hbotTop : (⊥ : unitInterval) < ⊤ := by
    norm_num [unitInterval]
  obtain ⟨u, _, hu, hulim⟩ :=
    RationalCoordinate.denseRange_toUnitInterval.exists_seq_strictMono_tendsto_of_lt
      htoMono hbotTop
  have htimeLimit : Tendsto (fun n => RationalCoordinate.toNNReal (u n)) atTop
      (𝓝 (1 : ℝ≥0)) := by
    rw [← NNReal.tendsto_coe]
    simpa [RationalCoordinate.toNNReal_coe, Function.comp_def] using
      (continuous_subtype_val.tendsto ⊤).comp hulim
  have htimeWithin : Tendsto (fun n => RationalCoordinate.toNNReal (u n)) atTop
      (𝓝[<] (1 : ℝ≥0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨htimeLimit, Filter.Eventually.of_forall fun n => ?_⟩
    have hbelow := (hu n).2
    have hbelowReal : ((u n : ℚ) : ℝ) < 1 := by
      change RationalCoordinate.toUnitInterval (u n) < ⊤ at hbelow
      exact hbelow
    have hbelowTime : (RationalCoordinate.toNNReal (u n) : ℝ) < 1 := by
      change ((u n : ℚ) : ℝ) < 1
      exact hbelowReal
    exact NNReal.coe_lt_coe.mp hbelowTime
  have hpathLimit : Tendsto (fun n => X (RationalCoordinate.toNNReal (u n)) ω) atTop
      (𝓝 (X 1 ω)) := by
    rw [← hωjump]
    exact (tendsto_leftLim_of_tendsto (hω.tendsto_nhdsLT 1)).comp htimeWithin
  have htopBound (q : RationalCoordinate.UnitInterval) (hq : q < ⊤) :
      |X (RationalCoordinate.toNNReal q) ω - X 1 ω| ≤ width := by
    have hdiff : Tendsto (fun n => X (RationalCoordinate.toNNReal q) ω -
        X (RationalCoordinate.toNNReal (u n)) ω) atTop
        (𝓝 (X (RationalCoordinate.toNNReal q) ω - X 1 ω)) :=
      tendsto_const_nhds.sub hpathLimit
    have habs : Tendsto (fun n => |X (RationalCoordinate.toNNReal q) ω -
        X (RationalCoordinate.toNNReal (u n)) ω|) atTop
        (𝓝 |X (RationalCoordinate.toNNReal q) ω - X 1 ω|) :=
      (continuous_abs.tendsto _).comp hdiff
    have hbounded : ∀ᶠ n in atTop,
        |X (RationalCoordinate.toNNReal q) ω - X (RationalCoordinate.toNNReal (u n)) ω| ∈
          Set.Iic width :=
      Filter.Eventually.of_forall fun n => hinterior q (u n) hq (by
        change (u n : ℚ) < 1
        have hbelow := (hu n).2
        have hbelowReal : ((u n : ℚ) : ℝ) < 1 := by
          change RationalCoordinate.toUnitInterval (u n) < ⊤ at hbelow
          exact hbelow
        exact_mod_cast hbelowReal)
    exact isClosed_Iic.mem_of_tendsto habs hbounded
  by_cases hs : s = ⊤
  · subst s
    by_cases ht : t = ⊤
    · have hwidth0 : 0 ≤ width := by
        have hbotTopQ : (⊥ : RationalCoordinate.UnitInterval) < ⊤ := by
          change (0 : ℚ) < 1
          norm_num
        simpa using hinterior ⊥ ⊥ hbotTopQ hbotTopQ
      simp [ht, hwidth0]
    · have ht' : t < ⊤ := lt_of_le_of_ne le_top ht
      have htopTime : RationalCoordinate.toNNReal ⊤ = 1 :=
        RationalCoordinate.toNNReal_top
      rw [htopTime]
      simpa [abs_sub_comm] using htopBound t ht'
  · by_cases ht : t = ⊤
    · subst t
      rw [RationalCoordinate.toNNReal_top]
      exact htopBound s (lt_of_le_of_ne le_top hs)
    · exact hinterior s t (lt_of_le_of_ne le_top hs) (lt_of_le_of_ne le_top ht)

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
        X (0 + 1 * unitInterval.toNNReal (RationalCoordinate.toUnitInterval q)) ω - X 0 ω ∧
      X (0 + 1 * unitInterval.toNNReal (RationalCoordinate.toUnitInterval q)) ω - X 0 ω ≤
        upper - margin at hq
    have htime : unitInterval.toNNReal (RationalCoordinate.toUnitInterval q) =
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
        X (0 + 1 * unitInterval.toNNReal (RationalCoordinate.toUnitInterval q)) ω - X 0 ω ∧
      X (0 + 1 * unitInterval.toNNReal (RationalCoordinate.toUnitInterval q)) ω - X 0 ω ≤
        width - margin
    have htime : unitInterval.toNNReal (RationalCoordinate.toUnitInterval q) =
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
      have htime : unitInterval.toNNReal (RationalCoordinate.toUnitInterval q) =
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
    · have hbot : unitInterval.toNNReal (⊥ : unitInterval) = 0 := by
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

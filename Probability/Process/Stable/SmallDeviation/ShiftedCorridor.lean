/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.FiniteTimeEntrance
public import Probability.Process.Stable.SmallDeviation.Blocks.EntranceFactorization
public import Probability.Process.Stable.SmallDeviation.Blocks.EntranceScaling
public import Probability.Process.Stable.SmallDeviation.Blocks.Upper.Shrinking
public import Probability.Distributions.Stable.Sign
public import Probability.Process.Path.Skorokhod.Corridor.Segment
public import Analysis.Asymptotics.NegativeRatio
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithmic comparison for shifted corridors

The entrance may take any fixed positive finite time. Stable scaling places
it in an initial interval of length `T * a ^ α`; independent increments then
give the same logarithmic comparison as a unit-time entrance.

This file compares small-deviation probabilities in translated intervals.
A positive-probability entrance over a fixed finite time gives a
multiplicative comparison after stable scaling.

## References

The comparison implies Lemma 2(a), equation (21), in Mogulskii's paper.

This is the light public entry point for shifted-corridor comparisons. It does
not import the feedback, path-support, or Poisson entrance arguments.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped NNReal Topology

/-- A fixed-time entrance, scaled into an initial interval of length
`T * a ^ α`, gives the finite-scale shifted-corridor inequality. -/
theorem IsStableLevyProcess.measure_shiftedFullCorridor_ge_entrance_mul_finiteTime
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (a : ℝ) (ha : 0 < a)
    (T : ℝ≥0) (hT : 0 < T) (hcut : T * stableEntranceHorizon α a < 1)
    (b c ε : ℝ) (hε : 0 ≤ ε) :
    P (fullSegmentCorridorEvent X 0 1 (a * (b - 1)) (a * (b + 1))) *
      P (fullSegmentCorridorReturnEvent X 0 T
        (c - 1) (c + 1) (c - b - ε) (c - b + ε)) ≤
    P (fullSegmentCorridorEvent X 0 1
      (a * (c - (1 + ε))) (a * (c + 1 + ε))) := by
  let cut : ℝ≥0 := T * stableEntranceHorizon α a
  let remaining : ℝ≥0 := 1 - cut
  have hcutPos : 0 < cut := by
    dsimp [cut]
    exact mul_pos hT (by
      apply NNReal.coe_pos.mp
      simp [stableEntranceHorizon,
        Real.coe_toNNReal _ (Real.rpow_pos_of_pos ha α).le]
      exact Real.rpow_pos_of_pos ha α)
  have hcutlt : cut < 1 := by
    simpa [cut] using hcut
  have hremaining : 0 < remaining := tsub_pos_iff_lt.mpr hcutlt
  have hsum : cut + remaining = 1 := add_tsub_cancel_of_le hcutlt.le
  have hα : 0 < α := h.increments.strictlyStable.1
  have hhor : (stableEntranceHorizon α a : ℝ) = a ^ α := by
    simp [stableEntranceHorizon,
      Real.coe_toNNReal _ (Real.rpow_pos_of_pos ha α).le]
  have hscale : (cut : ℝ) ^ (-(1 / α)) =
      (T : ℝ) ^ (-(1 / α)) * a⁻¹ := by
    change ((T * stableEntranceHorizon α a : ℝ≥0) : ℝ) ^
      (-(1 / α)) = _
    rw [NNReal.coe_mul, hhor]
    rw [Real.mul_rpow (NNReal.coe_nonneg T) (Real.rpow_nonneg ha.le α)]
    rw [← Real.rpow_mul ha.le]
    have hexp : α * (-(1 / α)) = -1 := by
      field_simp [ne_of_gt hα]
    rw [hexp, Real.rpow_neg_one]
  have hcutScale := h.measure_fullSegmentCorridorReturn_scale cut hcutPos
    (a * (c - 1)) (a * (c + 1))
    (a * (c - b - ε)) (a * (c - b + ε))
  rw [hscale] at hcutScale
  have hTScale := h.measure_fullSegmentCorridorReturn_scale T hT
    (c - 1) (c + 1) (c - b - ε) (c - b + ε)
  have hcancel (x : ℝ) :
      a * x * ((T : ℝ) ^ (-(1 / α)) * a⁻¹) =
        x * (T : ℝ) ^ (-(1 / α)) := by
    field_simp [ha.ne']
  rw [hcancel (c - 1), hcancel (c + 1),
    hcancel (c - b - ε), hcancel (c - b + ε)] at hcutScale
  have hfirstEq :
      P (fullSegmentCorridorReturnEvent X 0 cut
        (a * (c - 1)) (a * (c + 1))
        (a * (c - b - ε)) (a * (c - b + ε))) =
      P (fullSegmentCorridorReturnEvent X 0 T
        (c - 1) (c + 1) (c - b - ε) (c - b + ε)) := by
    exact hcutScale.trans hTScale.symm
  have hmono :
      fullSegmentCorridorReturnEvent X 0 cut
        (a * (c - 1)) (a * (c + 1))
        (a * (c - b - ε)) (a * (c - b + ε)) ⊆
      fullSegmentCorridorReturnEvent X 0 cut
        (a * (c - (1 + ε))) (a * (c + 1 + ε))
        (a * (c - b - ε)) (a * (c - b + ε)) := by
    apply fullSegmentCorridorReturnEvent_mono_bounds X 0 cut
    · nlinarith [mul_nonneg ha.le hε]
    · nlinarith [mul_nonneg ha.le hε]
    · exact le_rfl
    · exact le_rfl
  have hbound := h.measure_fullCorridor_ge_entrance_mul_fullCorridor
    cut remaining hcutPos hremaining
    (a * (c - (1 + ε))) (a * (c + 1 + ε))
    (a * (c - b - ε)) (a * (c - b + ε))
  rw [hsum] at hbound
  have hlo : a * (c - (1 + ε)) - a * (c - b - ε) = a * (b - 1) := by ring
  have hhi : a * (c + 1 + ε) - a * (c - b + ε) = a * (b + 1) := by ring
  rw [hlo, hhi] at hbound
  have hfirst :
      P (fullSegmentCorridorReturnEvent X 0 cut
        (a * (c - (1 + ε))) (a * (c + 1 + ε))
        (a * (c - b - ε)) (a * (c - b + ε))) ≥
      P (fullSegmentCorridorReturnEvent X 0 T
        (c - 1) (c + 1) (c - b - ε) (c - b + ε)) := by
    rw [← hfirstEq]
    exact measure_mono hmono
  calc
    _ = P (fullSegmentCorridorReturnEvent X 0 T
        (c - 1) (c + 1) (c - b - ε) (c - b + ε)) *
        P (fullSegmentCorridorEvent X 0 1
          (a * (b - 1)) (a * (b + 1))) := mul_comm _ _
    _ ≤ P (fullSegmentCorridorReturnEvent X 0 cut
          (a * (c - (1 + ε))) (a * (c + 1 + ε))
          (a * (c - b - ε)) (a * (c - b + ε))) *
        P (fullSegmentCorridorEvent X 0 1
          (a * (b - 1)) (a * (b + 1))) := by
          exact mul_le_mul_of_nonneg_right hfirst bot_le
    _ ≤ _ := hbound

/-- The fixed-time entrance gives the logarithmic bound with its positive
probability as a constant multiplicative factor. -/
theorem IsStableLevyProcess.log_measure_narrow_le_log_measure_wide_sub_fixedTimeEntrance
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (a : ℝ) (ha : 0 < a)
    (T : ℝ≥0) (hT : 0 < T) (hcut : T * stableEntranceHorizon α a < 1)
    (b c ε : ℝ) (hε : 0 ≤ ε)
    (hp : 0 < P (fullSegmentCorridorReturnEvent X 0 T
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)))
    (hq : 0 < P (fullSegmentCorridorEvent X 0 1
      (a * (b - 1)) (a * (b + 1)))) :
    Real.log ((P (fullSegmentCorridorEvent X 0 1
        (a * (b - 1)) (a * (b + 1)))).toReal) ≤
      Real.log ((P (fullSegmentCorridorEvent X 0 1
        (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal) -
      Real.log ((P (fullSegmentCorridorReturnEvent X 0 T
        (c - 1) (c + 1) (c - b - ε) (c - b + ε))).toReal) := by
  let p := P (fullSegmentCorridorReturnEvent X 0 T
    (c - 1) (c + 1) (c - b - ε) (c - b + ε))
  let q := P (fullSegmentCorridorEvent X 0 1
    (a * (b - 1)) (a * (b + 1)))
  let r := P (fullSegmentCorridorEvent X 0 1
    (a * (c - (1 + ε))) (a * (c + 1 + ε)))
  have hp' : 0 < p.toReal := ENNReal.toReal_pos_iff.mpr
    ⟨hp, (measure_lt_top P _ )⟩
  have hq' : 0 < q.toReal := ENNReal.toReal_pos_iff.mpr
    ⟨hq, (measure_lt_top P _ )⟩
  have hrFinite : r ≠ ⊤ := (measure_lt_top P _).ne
  have hbound' := h.measure_shiftedFullCorridor_ge_entrance_mul_finiteTime
    a ha T hT hcut b c ε hε
  have hbound : p * q ≤ r := by
    calc
      _ = q * p := mul_comm _ _
      _ ≤ r := by simpa [p, q, r] using hbound'
  have hboundReal : p.toReal * q.toReal ≤ r.toReal := by
    rw [← ENNReal.toReal_mul]
    exact (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top
      (measure_lt_top P _).ne (measure_lt_top P _).ne) hrFinite).mpr hbound
  have hlog := Real.log_le_log (mul_pos hp' hq') hboundReal
  rw [Real.log_mul hp'.ne' hq'.ne'] at hlog
  change Real.log q.toReal ≤ Real.log r.toReal - Real.log p.toReal
  linarith

/-- A fixed finite-time entrance proves relation (21) without a unit-time
entrance assumption. The positive entrance factor is constant in `a`, so its
logarithm is negligible compared with the diverging wide-corridor logarithm. -/
theorem IsStableLevyProcess.eventually_one_sub_le_log_corridor_ratio_of_entrance
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hpos : 0 < μ (Set.Ioi 0)) (hneg : 0 < μ (Set.Iio 0))
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1) (hε : 0 ≤ ε)
    (T : ℝ≥0) (hT : 0 < T)
    (hp : 0 < P (fullSegmentCorridorReturnEvent X 0 T
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 - δ ≤
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (b - 1)) (a * (b + 1)))).toReal) /
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let narrow : ℝ → ℝ := fun a => Real.log ((P
    (fullSegmentCorridorEvent X 0 1
      (a * (b - 1)) (a * (b + 1)))).toReal)
  let wide : ℝ → ℝ := fun a => Real.log ((P
    (fullSegmentCorridorEvent X 0 1
      (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal)
  let C : ℝ := -Real.log ((P (fullSegmentCorridorReturnEvent X 0 T
    (c - 1) (c + 1) (c - b - ε) (c - b + ε))).toReal)
  have hα : 0 < α := h.increments.strictlyStable.1
  have hpow : Tendsto (fun a : ℝ => a ^ α) l (nhds 0) := by
    have hcont := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
    simpa [Real.zero_rpow hα.ne'] using
      (hcont.mono_left (nhdsWithin_le_nhds : l ≤ nhds 0))
  have hcutT : Tendsto (fun a : ℝ => (T : ℝ) * a ^ α) l (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hpow :
        Tendsto (fun a : ℝ => (T : ℝ) * a ^ α) l
          (nhds ((T : ℝ) * 0)))
  have hcutSmall : ∀ᶠ a : ℝ in l, (T : ℝ) * a ^ α < 1 := by
    filter_upwards [hcutT.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with a ha
    exact ha
  have hq : ∀ᶠ a : ℝ in l, 0 < P (fullSegmentCorridorEvent X 0 1
      (a * (b - 1)) (a * (b + 1))) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    apply h.measure_fullSegmentCorridor_pos
    · nlinarith [mul_pos ha (sub_pos.mpr hb.2)]
    · nlinarith [mul_pos ha (by linarith [hb.1] : 0 < b + 1)]
    · exact hpos
    · exact hneg
  have hwidePos : ∀ᶠ a : ℝ in l, 0 < P (fullSegmentCorridorEvent X 0 1
      (a * (c - (1 + ε))) (a * (c + 1 + ε))) := by
    filter_upwards [self_mem_nhdsWithin, hcutSmall, hq]
      with a ha hcut hqa
    have hTco : (T : ℝ) * (stableEntranceHorizon α a : ℝ) =
        (T : ℝ) * a ^ α := by
      rw [show (stableEntranceHorizon α a : ℝ) = a ^ α by
        simp [stableEntranceHorizon,
          Real.coe_toNNReal _ (Real.rpow_pos_of_pos ha α).le]]
    have hcut' : T * stableEntranceHorizon α a < 1 := by
      apply NNReal.coe_lt_one.mp
      change (T : ℝ) * (stableEntranceHorizon α a : ℝ) < 1
      rw [hTco]
      exact hcut
    have hbound := h.measure_shiftedFullCorridor_ge_entrance_mul_finiteTime
      a ha T hT hcut' b c ε hε
    exact (ENNReal.mul_pos hqa.ne' hp.ne').trans_le hbound
  have hwideZero : Tendsto (fun a : ℝ => P (fullSegmentCorridorEvent X 0 1
      (a * (c - (1 + ε))) (a * (c + 1 + ε)))) l (nhds 0) :=
    h.tendsto_measure_scaledFullCorridor_zero hpos
      (c - (1 + ε)) (c + 1 + ε)
  have hrealZero : Tendsto (fun a : ℝ =>
      (P (fullSegmentCorridorEvent X 0 1
        (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal) l (nhds 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hwideZero
  have hrealPos : ∀ᶠ a : ℝ in l, 0 <
      (P (fullSegmentCorridorEvent X 0 1
        (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal := by
    filter_upwards [hwidePos] with a ha
    exact ENNReal.toReal_pos_iff.mpr ⟨ha, measure_lt_top P _⟩
  have hrealGT : Tendsto (fun a : ℝ =>
      (P (fullSegmentCorridorEvent X 0 1
        (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal)
      l (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrealZero, hrealPos⟩
  have hwide : Tendsto wide l atBot := by
    simpa only [wide, Function.comp_def] using
      Real.tendsto_log_nhdsGT_zero.comp hrealGT
  have hfg : narrow ≤ᶠ[l] fun a => wide a + C := by
    filter_upwards [self_mem_nhdsWithin, hcutSmall, hq]
      with a ha hcut hqa
    have hTco : (T : ℝ) * (stableEntranceHorizon α a : ℝ) =
        (T : ℝ) * a ^ α := by
      rw [show (stableEntranceHorizon α a : ℝ) = a ^ α by
        simp [stableEntranceHorizon,
          Real.coe_toNNReal _ (Real.rpow_pos_of_pos ha α).le]]
    have hcut' : T * stableEntranceHorizon α a < 1 := by
      apply NNReal.coe_lt_one.mp
      change (T : ℝ) * (stableEntranceHorizon α a : ℝ) < 1
      rw [hTco]
      exact hcut
    have hlog := h.log_measure_narrow_le_log_measure_wide_sub_fixedTimeEntrance
      a ha T hT hcut' b c ε hε hp hqa
    dsimp [narrow, wide, C]
    linarith
  simpa only [narrow, wide, l] using
    Asymptotics.eventually_one_sub_le_ratio_of_additive_bound C hfg hwide δ hδ

/-- The fixed finite-time entrance is obtained from strict stability under the
source CDF condition. This is the direct Lemma 2(a), relation (21), route. -/
theorem IsStableLevyProcess.eventually_one_sub_le_log_corridor_ratio_of_cdf
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hε : 0 < ε)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 - δ ≤
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (b - 1)) (a * (b + 1)))).toReal) /
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal) := by
  obtain ⟨hneg, hpos⟩ :=
    h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
  obtain ⟨T, hT, hp⟩ :=
    h.exists_pos_time_measure_fullSegmentCorridorReturnEvent_pos
    (c - 1) (c + 1) (c - b) ε
    (by linarith [hc.1]) (by linarith [hc.2])
    (by linarith [hb.1, hb.2, hc.1])
    (by linarith [hb.1, hb.2, hc.2]) hε hcdf
  exact h.eventually_one_sub_le_log_corridor_ratio_of_entrance
    hpos hneg b c ε hb hε.le T hT hp δ hδ

/-- The source's strict left-half-line condition, expressed directly as
positive mass on `Iio 0`, implies the shifted-corridor comparison. -/
theorem IsStableLevyProcess.eventually_one_sub_le_log_corridor_ratio_of_measure_Iio_zero
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hleft : 0 < μ (Set.Iio 0) ∧ μ (Set.Iio 0) < 1)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hε : 0 < ε)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 - δ ≤
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (b - 1)) (a * (b + 1)))).toReal) /
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal) := by
  exact h.eventually_one_sub_le_log_corridor_ratio_of_cdf
    (h.increments.strictlyStable.cdfAtZero_condition_of_strictLeftMass hleft)
    b c ε hb hc hε δ hδ

end ProbabilityTheory

end

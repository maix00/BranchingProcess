module

public import Probability.Process.Stable.SmallDeviation.Blocks.EntranceFactorization
public import Probability.Process.Stable.SmallDeviation.Blocks.EntranceScaling
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Shifted corridor comparison

The full-path probability bound obtained by inserting a short entrance block
of duration `a ^ α`. This is the finite-scale inequality used in Mogulskii's
comparison of shifted intervals.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem IsStableLevyProcess.measure_shiftedFullCorridor_ge_entrance_mul
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (b c ε : ℝ) :
    P (fullSegmentCorridorReturnEvent X 0 1
        (c - (1 + ε)) (c + 1 + ε)
        (c - b - ε) (c - b + ε)) *
      P (fullSegmentCorridorEvent X 0 1
        (a * (b - 1)) (a * (b + 1))) ≤
      P (fullSegmentCorridorEvent X 0 1
        (a * (c - (1 + ε))) (a * (c + 1 + ε))) := by
  let cut := stableEntranceHorizon α a
  let remaining : ℝ≥0 := 1 - cut
  have hcut : cut < 1 :=
    stableEntranceHorizon_lt_one ha ha1 h.increments.strictlyStable.1
  have hcutPos : 0 < cut := by
    apply NNReal.coe_pos.mp
    simp [cut, stableEntranceHorizon,
      Real.coe_toNNReal _ (Real.rpow_pos_of_pos ha α).le]
    exact Real.rpow_pos_of_pos ha α
  have hremaining : 0 < remaining := tsub_pos_iff_lt.mpr hcut
  have hsum : cut + remaining = 1 := by
    exact add_tsub_cancel_of_le hcut.le
  have hbound := h.measure_fullCorridor_ge_entrance_mul_fullCorridor
    cut remaining hcutPos hremaining
    (a * (c - (1 + ε))) (a * (c + 1 + ε))
    (a * (c - b - ε)) (a * (c - b + ε))
  rw [hsum] at hbound
  have hscale := h.shortEntrance_fullCorridorReturn_probability a ha
    (c - (1 + ε)) (c + 1 + ε) (c - b - ε) (c - b + ε)
  change P (fullSegmentCorridorReturnEvent X 0 cut
      (a * (c - (1 + ε))) (a * (c + 1 + ε))
      (a * (c - b - ε)) (a * (c - b + ε))) = _ at hscale
  rw [hscale] at hbound
  convert hbound using 1 <;> congr 2 <;> ring

/-- The finite-scale logarithmic consequence of the shifted-corridor bound.
The entrance factor contributes only the fixed additive constant `-log p`. -/
theorem IsStableLevyProcess.log_measure_narrow_le_log_measure_wide_sub_entrance
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (b c ε : ℝ)
    (hp : 0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - (1 + ε)) (c + 1 + ε) (c - b - ε) (c - b + ε)))
    (hq : 0 < P (fullSegmentCorridorEvent X 0 1
      (a * (b - 1)) (a * (b + 1)))) :
    Real.log ((P (fullSegmentCorridorEvent X 0 1
        (a * (b - 1)) (a * (b + 1)))).toReal) ≤
      Real.log ((P (fullSegmentCorridorEvent X 0 1
        (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal) -
      Real.log ((P (fullSegmentCorridorReturnEvent X 0 1
        (c - (1 + ε)) (c + 1 + ε) (c - b - ε) (c - b + ε))).toReal) := by
  let p := P (fullSegmentCorridorReturnEvent X 0 1
    (c - (1 + ε)) (c + 1 + ε) (c - b - ε) (c - b + ε))
  let q := P (fullSegmentCorridorEvent X 0 1
    (a * (b - 1)) (a * (b + 1)))
  let r := P (fullSegmentCorridorEvent X 0 1
    (a * (c - (1 + ε))) (a * (c + 1 + ε)))
  have hp' : 0 < p.toReal := ENNReal.toReal_pos_iff.mpr
    ⟨hp, (measure_lt_top P _ )⟩
  have hq' : 0 < q.toReal := ENNReal.toReal_pos_iff.mpr
    ⟨hq, (measure_lt_top P _ )⟩
  have hrFinite : r ≠ ⊤ := (measure_lt_top P _).ne
  have hbound : p * q ≤ r :=
    h.measure_shiftedFullCorridor_ge_entrance_mul a ha ha1 b c ε
  have hboundReal : p.toReal * q.toReal ≤ r.toReal := by
    rw [← ENNReal.toReal_mul]
    exact (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top
      (measure_lt_top P _).ne (measure_lt_top P _).ne) hrFinite).mpr hbound
  have hlog := Real.log_le_log (mul_pos hp' hq') hboundReal
  rw [Real.log_mul hp'.ne' hq'.ne'] at hlog
  change Real.log q.toReal ≤ Real.log r.toReal - Real.log p.toReal
  linarith

/-- The fixed entrance probability contributes no term at the Mogulskii
scale `a ^ α`. -/
theorem tendsto_stableEntranceLogCorrection_zero
    (α : ℝ) (hα : 0 < α) (p : ENNReal) :
    Filter.Tendsto (fun a : ℝ => a ^ α * Real.log p.toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hpow : Filter.Tendsto (fun a : ℝ => a ^ α)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hcont := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
    simpa [Real.zero_rpow hα.ne'] using
      (hcont.mono_left (nhdsWithin_le_nhds :
        nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0))
  simpa using hpow.mul_const (Real.log p.toReal)

/-- The logarithmic comparison at the small-deviation exponent scale. The
rightmost term tends to zero as `a ↓ 0`. -/
theorem IsStableLevyProcess.scaledLog_measure_narrow_le_wide_sub_entrance
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (b c ε : ℝ)
    (hp : 0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - (1 + ε)) (c + 1 + ε) (c - b - ε) (c - b + ε)))
    (hq : 0 < P (fullSegmentCorridorEvent X 0 1
      (a * (b - 1)) (a * (b + 1)))) :
    a ^ α * Real.log ((P (fullSegmentCorridorEvent X 0 1
        (a * (b - 1)) (a * (b + 1)))).toReal) ≤
      a ^ α * Real.log ((P (fullSegmentCorridorEvent X 0 1
        (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal) -
      a ^ α * Real.log ((P (fullSegmentCorridorReturnEvent X 0 1
        (c - (1 + ε)) (c + 1 + ε) (c - b - ε) (c - b + ε))).toReal) := by
  have hlog := h.log_measure_narrow_le_log_measure_wide_sub_entrance
    a ha ha1 b c ε hp hq
  have hmul := mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg ha.le α)
  simpa only [mul_sub] using hmul

end ProbabilityTheory

end

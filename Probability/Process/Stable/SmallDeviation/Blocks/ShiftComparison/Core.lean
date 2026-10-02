module

public import Probability.Process.Stable.SmallDeviation.Blocks.EntranceFactorization
public import Probability.Process.Stable.SmallDeviation.Blocks.EntranceScaling
public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.FullCorridor
public import Probability.Process.Stable.SmallDeviation.Blocks.Upper.Shrinking
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Analysis.Asymptotics.NegativeRatio
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Stable corridor comparison core

Finite-scale entrance inequalities and their logarithmic consequences. These results consume an entrance probability as data and do not select a way to prove it.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped NNReal Topology

theorem IsStableLevyProcess.measure_shiftedFullCorridor_ge_entrance_mul
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (b c ε : ℝ) (hε : 0 ≤ ε) :
    P (fullSegmentCorridorReturnEvent X 0 1
        (c - 1) (c + 1)
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
    (c - 1) (c + 1) (c - b - ε) (c - b + ε)
  change P (fullSegmentCorridorReturnEvent X 0 cut
      (a * (c - 1)) (a * (c + 1))
      (a * (c - b - ε)) (a * (c - b + ε))) = _ at hscale
  have hmono :
      P (fullSegmentCorridorReturnEvent X 0 cut
        (a * (c - 1)) (a * (c + 1))
        (a * (c - b - ε)) (a * (c - b + ε))) ≤
      P (fullSegmentCorridorReturnEvent X 0 cut
        (a * (c - (1 + ε))) (a * (c + 1 + ε))
        (a * (c - b - ε)) (a * (c - b + ε))) := by
    apply measure_mono
    apply fullSegmentCorridorReturnEvent_mono_bounds X 0 cut
    · nlinarith [mul_nonneg ha.le hε]
    · nlinarith [mul_nonneg ha.le hε]
    · exact le_rfl
    · exact le_rfl
  rw [hscale] at hmono
  calc
    _ ≤ P (fullSegmentCorridorReturnEvent X 0 cut
          (a * (c - (1 + ε))) (a * (c + 1 + ε))
          (a * (c - b - ε)) (a * (c - b + ε))) *
        P (fullSegmentCorridorEvent X 0 1
          (a * (b - 1)) (a * (b + 1))) := by gcongr
    _ ≤ _ := by convert hbound using 1 <;> congr 2 <;> ring

/-- The finite-scale logarithmic consequence of the shifted-corridor bound.
The entrance factor contributes only the fixed additive constant `-log p`. -/
theorem IsStableLevyProcess.log_measure_narrow_le_log_measure_wide_sub_entrance
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (b c ε : ℝ) (hε : 0 ≤ ε)
    (hp : 0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)))
    (hq : 0 < P (fullSegmentCorridorEvent X 0 1
      (a * (b - 1)) (a * (b + 1)))) :
    Real.log ((P (fullSegmentCorridorEvent X 0 1
        (a * (b - 1)) (a * (b + 1)))).toReal) ≤
      Real.log ((P (fullSegmentCorridorEvent X 0 1
        (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal) -
      Real.log ((P (fullSegmentCorridorReturnEvent X 0 1
        (c - 1) (c + 1) (c - b - ε) (c - b + ε))).toReal) := by
  let p := P (fullSegmentCorridorReturnEvent X 0 1
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
  have hbound : p * q ≤ r :=
    h.measure_shiftedFullCorridor_ge_entrance_mul a ha ha1 b c ε hε
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
    (b c ε : ℝ) (hε : 0 ≤ ε)
    (hp : 0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)))
    (hq : 0 < P (fullSegmentCorridorEvent X 0 1
      (a * (b - 1)) (a * (b + 1)))) :
    a ^ α * Real.log ((P (fullSegmentCorridorEvent X 0 1
        (a * (b - 1)) (a * (b + 1)))).toReal) ≤
      a ^ α * Real.log ((P (fullSegmentCorridorEvent X 0 1
        (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal) -
      a ^ α * Real.log ((P (fullSegmentCorridorReturnEvent X 0 1
        (c - 1) (c + 1) (c - b - ε) (c - b + ε))).toReal) := by
  have hlog := h.log_measure_narrow_le_log_measure_wide_sub_entrance
    a ha ha1 b c ε hε hp hq
  have hmul := mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg ha.le α)
  simpa only [mul_sub] using hmul

/-- The ratio form of the negative-logarithm comparison used in the original
notation. For every positive tolerance, the ratio is eventually at least
`1 - tolerance`; the fixed entrance cost disappears because the wide-tube
logarithm tends to negative infinity. -/
theorem IsStableLevyProcess.eventually_one_sub_le_logCorridor_ratio
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (b c ε : ℝ) (hε : 0 ≤ ε)
    (hp : 0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)))
    (hq : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < P (fullSegmentCorridorEvent X 0 1
        (a * (b - 1)) (a * (b + 1))))
    (hwide : Filter.Tendsto (fun a : ℝ =>
      Real.log ((P (fullSegmentCorridorEvent X 0 1
        (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal))
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 - δ ≤
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (b - 1)) (a * (b + 1)))).toReal) /
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let narrow : ℝ → ℝ := fun a =>
    Real.log ((P (fullSegmentCorridorEvent X 0 1
      (a * (b - 1)) (a * (b + 1)))).toReal)
  let wide : ℝ → ℝ := fun a =>
    Real.log ((P (fullSegmentCorridorEvent X 0 1
      (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal)
  let C : ℝ := -Real.log ((P (fullSegmentCorridorReturnEvent X 0 1
    (c - 1) (c + 1) (c - b - ε) (c - b + ε))).toReal)
  have ha : ∀ᶠ a : ℝ in l, 0 < a := self_mem_nhdsWithin
  have ha1 : ∀ᶠ a : ℝ in l, a < 1 :=
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hfg : narrow ≤ᶠ[l] fun a => wide a + C := by
    filter_upwards [ha, ha1, hq] with a ha ha1 hq
    have hlog := h.log_measure_narrow_le_log_measure_wide_sub_entrance
      a ha ha1 b c ε hε hp hq
    dsimp [narrow, wide, C]
    linarith
  simpa only [narrow, wide, l] using
    Asymptotics.eventually_one_sub_le_ratio_of_additive_bound C hfg hwide δ hδ

/-- A shrinking complete-path corridor has vanishing probability under a
positive-tail condition. The finite-block tube upper bound supplies this
without an atomlessness assumption on the increment law. -/
theorem IsStableLevyProcess.tendsto_measure_shiftedFullCorridor_zero
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hpos : 0 < μ (Set.Ioi 0)) (c ε : ℝ) :
    Filter.Tendsto (fun a : ℝ =>
      P (fullSegmentCorridorEvent X 0 1
        (a * (c - (1 + ε))) (a * (c + 1 + ε))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  h.tendsto_measure_scaledFullCorridor_zero hpos
    (c - (1 + ε)) (c + 1 + ε)

/-- Positivity of the fixed entrance event and eventual positivity of the
narrow corridor imply that the wide-corridor logarithm tends to negative
infinity, using the positive tail of the stable law. -/
theorem IsStableLevyProcess.tendsto_log_measure_shiftedFullCorridor_atBot
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hpos : 0 < μ (Set.Ioi 0))
    (b c ε : ℝ) (hε : 0 ≤ ε)
    (hp : 0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)))
    (hq : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < P (fullSegmentCorridorEvent X 0 1
        (a * (b - 1)) (a * (b + 1)))) :
    Filter.Tendsto (fun a : ℝ =>
      Real.log ((P (fullSegmentCorridorEvent X 0 1
        (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal))
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
  let wide : ℝ → ENNReal := fun a =>
    P (fullSegmentCorridorEvent X 0 1
      (a * (c - (1 + ε))) (a * (c + 1 + ε)))
  have ha : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < a :=
    self_mem_nhdsWithin
  have ha1 : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0), a < 1 :=
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hwidePos : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < wide a := by
    filter_upwards [ha, ha1, hq] with a ha ha1 hq
    exact (ENNReal.mul_pos hp.ne' hq.ne').trans_le
      (h.measure_shiftedFullCorridor_ge_entrance_mul a ha ha1 b c ε hε)
  have hwideZero : Filter.Tendsto wide
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    h.tendsto_measure_shiftedFullCorridor_zero hpos c ε
  have hrealZero : Filter.Tendsto (fun a => (wide a).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hwideZero
  have hrealPos : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < (wide a).toReal := by
    filter_upwards [hwidePos] with a ha
    exact ENNReal.toReal_pos_iff.mpr ⟨ha, (measure_lt_top P _ )⟩
  have hrealGT : Filter.Tendsto (fun a => (wide a).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrealZero, hrealPos⟩
  simpa only [wide, Function.comp_def] using
    Real.tendsto_log_nhdsGT_zero.comp hrealGT

/-- The ratio comparison for the negative logarithms, with the endpoint-law
positive-tail assumption discharging the divergence condition. The one
remaining probability input is positivity of the fixed entrance event. -/
theorem IsStableLevyProcess.eventually_one_sub_le_logCorridor_ratio_of_positiveTail
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hpos : 0 < μ (Set.Ioi 0))
    (b c ε : ℝ) (hε : 0 ≤ ε)
    (hp : 0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)))
    (hq : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < P (fullSegmentCorridorEvent X 0 1
        (a * (b - 1)) (a * (b + 1))))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 - δ ≤
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (b - 1)) (a * (b + 1)))).toReal) /
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal) := by
  exact h.eventually_one_sub_le_logCorridor_ratio b c ε hε hp hq
    (h.tendsto_log_measure_shiftedFullCorridor_atBot
      hpos b c ε hε hp hq) δ hδ

/-- Under two-sided increment mass, narrow corridors have positive
probability at every scale; only the fixed entrance event remains as an
explicit probabilistic input to the logarithmic comparison. -/
theorem IsStableLevyProcess.eventually_one_sub_le_logCorridor_ratio_of_entrance_pos
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hpos : 0 < μ (Set.Ioi 0)) (hneg : 0 < μ (Set.Iio 0))
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1) (hε : 0 ≤ ε)
    (hp : 0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 - δ ≤
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (b - 1)) (a * (b + 1)))).toReal) /
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal) := by
  have hq : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < P (fullSegmentCorridorEvent X 0 1
        (a * (b - 1)) (a * (b + 1))) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    apply h.measure_fullSegmentCorridor_pos
    · nlinarith [mul_pos ha (sub_pos.mpr hb.2)]
    · nlinarith [mul_pos ha (by linarith [hb.1] : 0 < b + 1)]
    · exact hpos
    · exact hneg
  exact h.eventually_one_sub_le_logCorridor_ratio_of_positiveTail
    hpos b c ε hε hp hq δ hδ

/-- When the entrance endpoint window already contains zero, its positive
probability follows from the general two-sided stable corridor theorem. -/
theorem IsStableLevyProcess.eventually_one_sub_le_logCorridor_ratio_of_small_shift
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hpos : 0 < μ (Set.Ioi 0)) (hneg : 0 < μ (Set.Iio 0))
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1) (hc : -1 < c ∧ c < 1)
    (hshift : |c - b| < ε)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 - δ ≤
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (b - 1)) (a * (b + 1)))).toReal) /
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal) := by
  have hε : 0 < ε := lt_of_le_of_lt (abs_nonneg _) hshift
  have hshift' := abs_lt.mp hshift
  have hp : 0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)) :=
    h.measure_fullSegmentCorridorReturn_pos_of_zero_mem
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)
      (by linarith [hc.2]) (by linarith [hc.1])
      (by linarith [hshift'.2]) (by linarith [hshift'.1]) hpos hneg
  exact h.eventually_one_sub_le_logCorridor_ratio_of_entrance_pos
    hpos hneg b c ε hb hε.le hp δ hδ


end ProbabilityTheory

end

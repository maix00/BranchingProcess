/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.Stable.SmallDeviation.EscapeRate.Corridor
import Probability.Process.Stable.SmallDeviation.EndpointComparison

/-! # Endpoint-constrained escape rates

The endpoint comparison is built from the stable escape-rate limits and the
source's exact left-open, right-closed terminal interval.
-/

@[expose] public section

namespace ProbabilityTheory

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

/-- Probability of a translated corridor with the source's left-open,
right-closed terminal window. The terminal interval is translated by the
same amount as the corridor. -/
def shiftedEndpointCorridorProbability
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (d c b a : ℝ) : ℝ≥0∞ :=
  P (fullSegmentCorridorIocReturnEvent X 0 1
    (a * (d - 1)) (a * (d + 1)) (a * (d + c)) (a * (d + b)))

/-- The normalized logarithmic probability of a translated corridor with a
terminal window. -/
noncomputable def stableShiftedEndpointCorridorLogRate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (α d c b a : ℝ) : ℝ :=
  a ^ α * Real.log ((shiftedEndpointCorridorProbability P X d c b a).toReal)

private def centeredEndpointComparisonProbability
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (ε c b a : ℝ) : ℝ≥0∞ :=
  P (fullSegmentCorridorIocReturnEvent X 0 1
    (-(1 + ε) * a) ((1 + ε) * a) (a * c) (a * b))

private theorem endpoint_log_bound_of_ratio
    {q e : ℝ≥0∞} {δ : ℝ}
    (hδ1 : δ < 1)
    (hqlog : Real.log q.toReal < 0)
    (hratio : 1 - δ ≤ Real.log q.toReal / Real.log e.toReal) :
    0 < e.toReal ∧ Real.log e.toReal < 0 ∧
      Real.log q.toReal / (1 - δ) ≤ Real.log e.toReal := by
  have hratioPos : 0 < Real.log q.toReal / Real.log e.toReal :=
    lt_of_lt_of_le (sub_pos.mpr hδ1) hratio
  have helogNeg : Real.log e.toReal < 0 := by
    by_contra hnot
    rcases lt_or_eq_of_le (le_of_not_gt hnot) with hpos | heq
    · have hnegRatio := div_neg_of_neg_of_pos hqlog hpos
      linarith
    · have heq' : Real.log e.toReal = 0 := heq.symm
      rw [heq'] at hratio
      simp only [div_zero] at hratio
      linarith
  have hepos : 0 < e.toReal := by
    by_contra hnot
    have hle : e.toReal ≤ 0 := le_of_not_gt hnot
    have heq : e.toReal = 0 := le_antisymm hle (ENNReal.toReal_nonneg)
    simp [heq] at helogNeg
  refine ⟨hepos, helogNeg, ?_⟩
  exact (div_le_iff₀ (sub_pos.mpr hδ1)).2
    (by simpa [mul_comm] using (le_div_iff_of_neg helogNeg).mp hratio)

private noncomputable def endpointTailScale (α T ρ a : ℝ) : ℝ :=
  ((1 - 2 * ρ) * a) / (1 - T * a ^ α) ^ (1 / α)

private theorem tendsto_endpointTailScale
    {α T ρ : ℝ} (hα : 0 < α) (hρ2 : 2 * ρ < 1) :
    Tendsto (endpointTailScale α T ρ) (𝓝[>] (0 : ℝ))
      (𝓝[>] (0 : ℝ)) := by
  let l := 𝓝[>] (0 : ℝ)
  have hpow : Tendsto (fun a : ℝ => a ^ α) l (𝓝 0) := by
    have hcont := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
    simpa [Real.zero_rpow hα.ne'] using
      (hcont.mono_left (nhdsWithin_le_nhds : l ≤ 𝓝 0))
  have hcut : Tendsto (fun a : ℝ => T * a ^ α) l (𝓝 0) :=
    by simpa using hpow.const_mul T
  have hremaining : Tendsto (fun a : ℝ => 1 - T * a ^ α) l (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hcut
  have hkappa : Tendsto (fun a : ℝ => (1 - T * a ^ α) ^ (1 / α))
      l (𝓝 1) := by
    have hcont := (Real.continuousAt_rpow_const 1 (1 / α)
      (Or.inl (by norm_num : (1 : ℝ) ≠ 0))).tendsto
    simpa only [Function.comp_def, Real.one_rpow] using hcont.comp hremaining
  have hinvkappa := hkappa.inv₀ one_ne_zero
  have hid : Tendsto id l (𝓝 (0 : ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hnumerator : Tendsto (fun a : ℝ => (1 - 2 * ρ) * a) l (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hid :
      Tendsto (fun a : ℝ => (1 - 2 * ρ) * a) l (𝓝 ((1 - 2 * ρ) * 0)))
  have hscaleZero : Tendsto (endpointTailScale α T ρ) l (𝓝 0) := by
    have hp := hnumerator.mul hinvkappa
    change Tendsto (fun a : ℝ =>
      ((1 - 2 * ρ) * a) / (1 - T * a ^ α) ^ (1 / α)) l (𝓝 0)
    simpa [div_eq_mul_inv] using hp
  have hscalePos : ∀ᶠ a : ℝ in l, 0 < endpointTailScale α T ρ a := by
    filter_upwards [self_mem_nhdsWithin,
      hkappa.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with a ha hκ
    exact div_pos (mul_pos (by linarith [hρ2]) ha) hκ
  change Tendsto (endpointTailScale α T ρ)
    (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0))
  exact tendsto_nhdsWithin_iff.mpr ⟨hscaleZero, hscalePos⟩

private theorem eventually_shiftedEndpoint_probability_ge_endpointComparison
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (d c b ρ : ℝ)
    (hc : -1 < c) (hb : b ≤ 1)
    (hρ : 0 < ρ) (hρgap : 4 * ρ < b - c)
    (T : ℝ≥0) (hT : 0 < T)
    :
    ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
      P (fullSegmentCorridorReturnEvent X 0
        (T * stableEntranceHorizon α a)
        (a * (d - 1)) (a * (d + 1))
        (a * (d - ρ)) (a * (d + ρ))) *
        centeredEndpointComparisonProbability P X ρ
          ((c + 2 * ρ) / (1 - 2 * ρ))
          ((b - 2 * ρ) / (1 - 2 * ρ))
          (endpointTailScale α T ρ a) ≤
      shiftedEndpointCorridorProbability P X d c b a := by
  let l := 𝓝[>] (0 : ℝ)
  have hα : 0 < α := h.increments.strictlyStable.1
  have hpow : Tendsto (fun a : ℝ => a ^ α) l (𝓝 0) := by
    have hcont := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
    simpa [Real.zero_rpow hα.ne'] using
      (hcont.mono_left (nhdsWithin_le_nhds : l ≤ 𝓝 0))
  have hcut : Tendsto (fun a : ℝ => (T : ℝ) * a ^ α) l (𝓝 0) :=
    by simpa using hpow.const_mul (T : ℝ)
  have hcutLt : ∀ᶠ a : ℝ in l, (T : ℝ) * a ^ α < 1 :=
    hcut.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hq : 0 < 1 - 2 * ρ := by nlinarith [hc, hb, hρgap]
  have hc0 : -1 ≤ (c + 2 * ρ) / (1 - 2 * ρ) := by
    rw [le_div_iff₀ hq]
    nlinarith [hc]
  have hcb0 : (c + 2 * ρ) / (1 - 2 * ρ) <
      (b - 2 * ρ) / (1 - 2 * ρ) := by
    apply div_lt_div_of_pos_right _ hq
    nlinarith [hρgap]
  have hb0 : (b - 2 * ρ) / (1 - 2 * ρ) ≤ 1 := by
    rw [div_le_one hq]
    linarith [hb]
  filter_upwards [self_mem_nhdsWithin, hcutLt] with a ha hsmall
  let cut : ℝ≥0 := T * stableEntranceHorizon α a
  let remaining : ℝ≥0 := 1 - cut
  have hhor : (stableEntranceHorizon α a : ℝ) = a ^ α := by
    simp [stableEntranceHorizon,
      Real.coe_toNNReal _ (Real.rpow_pos_of_pos ha α).le]
  have hcutval : (cut : ℝ) = (T : ℝ) * a ^ α := by
    simp [cut, NNReal.coe_mul, hhor]
  have hcutlt : cut < 1 := by
    apply NNReal.coe_lt_one.mp
    rw [hcutval]
    exact hsmall
  have hcutpos : 0 < cut := by
    dsimp [cut]
    exact mul_pos hT (by
      apply NNReal.coe_pos.mp
      rw [hhor]
      exact Real.rpow_pos_of_pos ha α)
  have hremaining : 0 < remaining := tsub_pos_iff_lt.mpr hcutlt
  have hsum : cut + remaining = 1 := add_tsub_cancel_of_le hcutlt.le
  have hremainReal : (remaining : ℝ) = 1 - (T : ℝ) * a ^ α := by
    simp [remaining, NNReal.coe_sub hcutlt.le, hcutval]
  let κ : ℝ := (remaining : ℝ) ^ (1 / α)
  have hκpos : 0 < κ := by
    dsimp [κ]
    exact Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hremaining) _
  have hs : endpointTailScale α (T : ℝ) ρ a =
      (1 - 2 * ρ) * a * κ⁻¹ := by
    dsimp [endpointTailScale, κ]
    rw [hremainReal]
    rw [div_eq_mul_inv]
  have hfirstScale := h.measure_scaled_time_fullReturn a ha T hT
    (d - 1) (d + 1) (d - ρ) (d + ρ)
  let firstProb : ℝ≥0∞ :=
    P (fullSegmentCorridorReturnEvent X 0 cut
      (a * (d - 1)) (a * (d + 1))
      (a * (d - ρ)) (a * (d + ρ)))
  have hfirstEq : firstProb =
      P (fullSegmentCorridorReturnEvent X 0 T
        (d - 1) (d + 1) (d - ρ) (d + ρ)) := by
    simpa [firstProb, cut] using hfirstScale
  let tailLower : ℝ := -a * (1 - ρ)
  let tailUpper : ℝ := a * (1 - ρ)
  let tailCoreLower : ℝ := a * (c + 2 * ρ)
  let tailCoreUpper : ℝ := a * (b - ρ)
  let tailAtCut : ℝ≥0∞ :=
    P (fullSegmentCorridorReturnEvent X cut remaining
      tailLower tailUpper tailCoreLower tailCoreUpper)
  let tailAtZero : ℝ≥0∞ :=
    P (fullSegmentCorridorReturnEvent X 0 remaining
      tailLower tailUpper tailCoreLower tailCoreUpper)
  have hshift := h.measure_fullSegmentCorridorReturn_shift cut remaining
    tailLower tailUpper tailCoreLower tailCoreUpper
  have htailShift : tailAtZero = tailAtCut := by
    simpa [tailAtZero, tailAtCut] using hshift
  have htailScale := h.measure_fullSegmentCorridorReturn_scale remaining
    hremaining tailLower tailUpper tailCoreLower tailCoreUpper
  let tailAtUnit : ℝ≥0∞ :=
    P (fullSegmentCorridorReturnEvent X 0 1
      (tailLower * ((remaining : ℝ) ^ (-(1 / α))))
      (tailUpper * ((remaining : ℝ) ^ (-(1 / α))))
      (tailCoreLower * ((remaining : ℝ) ^ (-(1 / α))))
      (tailCoreUpper * ((remaining : ℝ) ^ (-(1 / α)))))
  have htailScaled : tailAtZero = tailAtUnit := by
    simpa [tailAtZero, tailAtUnit] using htailScale
  let s : ℝ := endpointTailScale α (T : ℝ) ρ a
  have hsκ : s = (1 - 2 * ρ) * a * κ⁻¹ := by
    exact hs
  have hscaledEvent :
      fullSegmentCorridorIocReturnEvent X 0 1
        (-(1 + ρ) * s) ((1 + ρ) * s)
        (s * ((c + 2 * ρ) / (1 - 2 * ρ)))
        (s * ((b - 2 * ρ) / (1 - 2 * ρ))) ⊆
      fullSegmentCorridorReturnEvent X 0 1
        (tailLower * ((remaining : ℝ) ^ (-(1 / α))))
        (tailUpper * ((remaining : ℝ) ^ (-(1 / α))))
        (tailCoreLower * ((remaining : ℝ) ^ (-(1 / α))))
        (tailCoreUpper * ((remaining : ℝ) ^ (-(1 / α)))) := by
    have hscaleK : (remaining : ℝ) ^ (-(1 / α)) = κ⁻¹ := by
      dsimp [κ]
      exact Real.rpow_neg (NNReal.coe_nonneg remaining) (1 / α)
    have hunitPos : 0 < a * κ⁻¹ := mul_pos ha (inv_pos.mpr hκpos)
    have houter : (1 + ρ) * (1 - 2 * ρ) ≤ 1 - ρ := by nlinarith
    have hcoreUpper : b - 2 * ρ < b - ρ := by linarith
    have hsourceLo : -(1 + ρ) * s =
        (-(a * (1 - ρ - 2 * ρ ^ 2))) * κ⁻¹ := by
      rw [hsκ]
      ring
    have hsourceHi : (1 + ρ) * s =
        (a * (1 - ρ - 2 * ρ ^ 2)) * κ⁻¹ := by
      rw [hsκ]
      ring
    have htargetLo : tailLower * ((remaining : ℝ) ^ (-(1 / α))) =
        (-(a * (1 - ρ))) * κ⁻¹ := by
      rw [hscaleK]
      dsimp [tailLower]
      ring
    have htargetHi : tailUpper * ((remaining : ℝ) ^ (-(1 / α))) =
        (a * (1 - ρ)) * κ⁻¹ := by
      rw [hscaleK]
    have hcoreLo : s * ((c + 2 * ρ) / (1 - 2 * ρ)) =
        tailCoreLower * κ⁻¹ := by
      rw [hsκ]
      dsimp [tailCoreLower]
      field_simp [ne_of_gt hq]
    have hcoreHi : s * ((b - 2 * ρ) / (1 - 2 * ρ)) =
        (a * (b - 2 * ρ)) * κ⁻¹ := by
      rw [hsκ]
      field_simp [ne_of_gt hq]
    rw [hsourceLo, hsourceHi, htargetLo, htargetHi, hcoreLo, hcoreHi]
    intro ω hω
    rcases hω with ⟨⟨margin, hmargin, hpath⟩, hend⟩
    refine ⟨⟨margin, hmargin, ?_⟩, ?_⟩
    · intro t
      obtain ⟨hlo, hhi⟩ := hpath t
      have hrad : (1 - ρ - 2 * ρ ^ 2) * (a * κ⁻¹) ≤
          (1 - ρ) * (a * κ⁻¹) :=
        mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg ρ])
          (le_of_lt hunitPos)
      constructor
      · nlinarith [hlo]
      · nlinarith [hhi, hrad]
    · change segmentIncrement X 0 1 ω ⊤ ∈
        Set.Ioo (tailCoreLower * ((remaining : ℝ) ^ (-(1 / α))))
          (tailCoreUpper * ((remaining : ℝ) ^ (-(1 / α))))
      change segmentIncrement X 0 1 ω ⊤ ∈
        Set.Ioc (tailCoreLower * κ⁻¹) ((a * (b - 2 * ρ)) * κ⁻¹) at hend
      constructor
      · rw [hscaleK]
        exact hend.1
      · rw [hscaleK]
        have hstrict : (a * (b - 2 * ρ)) * κ⁻¹ <
            tailCoreUpper * κ⁻¹ := by
          dsimp [tailCoreUpper]
          exact mul_lt_mul_of_pos_right
            (mul_lt_mul_of_pos_left hcoreUpper ha) (inv_pos.mpr hκpos)
        exact lt_of_le_of_lt hend.2 hstrict
  have htailLowerBound : centeredEndpointComparisonProbability P X ρ
      ((c + 2 * ρ) / (1 - 2 * ρ))
      ((b - 2 * ρ) / (1 - 2 * ρ)) s ≤ tailAtUnit := by
    change P _ ≤ P _
    exact measure_mono hscaledEvent
  have htailAtCutLower : centeredEndpointComparisonProbability P X ρ
      ((c + 2 * ρ) / (1 - 2 * ρ))
      ((b - 2 * ρ) / (1 - 2 * ρ)) s ≤ tailAtCut := by
    calc
      _ ≤ tailAtUnit := htailLowerBound
      _ = tailAtZero := htailScaled.symm
      _ = tailAtCut := htailShift
  have hglue := h.measure_fullReturn_ge_return_mul_return
    cut remaining hcutpos hremaining
    (a * (d - 1)) (a * (d + 1))
    (a * (d - ρ)) (a * (d + ρ))
    tailCoreLower tailCoreUpper
  rw [hsum] at hglue
  have hlowerDiff : a * (d - 1) - a * (d - ρ) = tailLower := by
    dsimp [tailLower]
    ring
  have hupperDiff : a * (d + 1) - a * (d + ρ) = tailUpper := by
    dsimp [tailUpper]
    ring
  rw [hlowerDiff, hupperDiff] at hglue
  have hsubset :
      fullSegmentCorridorReturnEvent X 0 1
        (a * (d - 1)) (a * (d + 1))
        (a * (d - ρ) + tailCoreLower)
        (a * (d + ρ) + tailCoreUpper) ⊆
      fullSegmentCorridorIocReturnEvent X 0 1
        (a * (d - 1)) (a * (d + 1))
        (a * (d + c)) (a * (d + b)) := by
    intro ω hω
    rcases hω with ⟨hcorr, hend⟩
    refine ⟨hcorr, ?_⟩
    constructor
    · dsimp [tailCoreLower] at hend ⊢
      have hlow : a * (d + c) < a * (d - ρ) + a * (c + 2 * ρ) := by
        nlinarith [mul_pos ha hρ]
      exact lt_trans hlow hend.1
    · dsimp [tailCoreUpper] at hend ⊢
      have hup : a * (d + ρ) + a * (b - ρ) = a * (d + b) := by ring
      rw [← hup]
      exact le_of_lt hend.2
  have hglue' :
      P (fullSegmentCorridorReturnEvent X 0 cut
        (a * (d - 1)) (a * (d + 1))
        (a * (d - ρ)) (a * (d + ρ))) *
        P (fullSegmentCorridorReturnEvent X cut remaining
          tailLower tailUpper tailCoreLower tailCoreUpper) ≤
      P (fullSegmentCorridorReturnEvent X 0 1
        (a * (d - 1)) (a * (d + 1))
        (a * (d - ρ) + tailCoreLower)
        (a * (d + ρ) + tailCoreUpper)) := by
    simpa [tailLower, tailUpper, tailCoreLower, tailCoreUpper,
      add_assoc, add_comm, add_left_comm] using hglue
  have hprob := calc
    P (fullSegmentCorridorReturnEvent X 0 cut
        (a * (d - 1)) (a * (d + 1))
        (a * (d - ρ)) (a * (d + ρ))) *
      centeredEndpointComparisonProbability P X ρ
        ((c + 2 * ρ) / (1 - 2 * ρ))
        ((b - 2 * ρ) / (1 - 2 * ρ)) s
        ≤
      P (fullSegmentCorridorReturnEvent X 0 cut
        (a * (d - 1)) (a * (d + 1))
        (a * (d - ρ)) (a * (d + ρ))) *
      P (fullSegmentCorridorReturnEvent X cut remaining
        (tailLower) (tailUpper) tailCoreLower tailCoreUpper) :=
          mul_le_mul_of_nonneg_left htailAtCutLower bot_le
    _ ≤ P (fullSegmentCorridorReturnEvent X 0 1
        (a * (d - 1)) (a * (d + 1))
        (a * (d - ρ) + tailCoreLower)
        (a * (d + ρ) + tailCoreUpper)) := hglue'
    _ ≤ shiftedEndpointCorridorProbability P X d c b a :=
          measure_mono hsubset
  simpa [s, endpointTailScale, stableEntranceHorizon,
    Real.coe_toNNReal _ (Real.rpow_pos_of_pos ha α).le,
    cut, firstProb] using hprob

private theorem eventually_shiftedEndpoint_ge_fixedEntrance_mul_endpointComparison
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (d c b ρ : ℝ)
    (hc : -1 < c) (hb : b ≤ 1)
    (hρ : 0 < ρ) (hρgap : 4 * ρ < b - c)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
      P (fullSegmentCorridorReturnEvent X 0 T
        (d - 1) (d + 1) (d - ρ) (d + ρ)) *
        centeredEndpointComparisonProbability P X ρ
          ((c + 2 * ρ) / (1 - 2 * ρ))
          ((b - 2 * ρ) / (1 - 2 * ρ))
          (endpointTailScale α T ρ a) ≤
        shiftedEndpointCorridorProbability P X d c b a := by
  have hglue := eventually_shiftedEndpoint_probability_ge_endpointComparison
    h d c b ρ hc hb hρ hρgap T hT
  filter_upwards [self_mem_nhdsWithin, hglue] with a ha hbound
  have hscale := h.measure_scaled_time_fullReturn a ha T hT
    (d - 1) (d + 1) (d - ρ) (d + ρ)
  have hfirst :
      P (fullSegmentCorridorReturnEvent X 0
        (T * stableEntranceHorizon α a)
        (a * (d - 1)) (a * (d + 1))
        (a * (d - ρ)) (a * (d + ρ))) =
      P (fullSegmentCorridorReturnEvent X 0 T
        (d - 1) (d + 1) (d - ρ) (d + ρ)) := by
    simpa using hscale
  rw [hfirst] at hbound
  simpa [shiftedEndpointCorridorProbability] using hbound

private noncomputable def endpointEscapeFactor (α ρ : ℝ) : ℝ :=
  (1 - ρ)⁻¹ * ((1 - 2 * ρ) ^ α)⁻¹

private noncomputable def endpointRateFactor (α T ρ a : ℝ) : ℝ :=
  ((a / endpointTailScale α T ρ a) ^ α) / (1 - ρ)

private theorem endpointRateFactor_eq
    {α T ρ a : ℝ} (hα : 0 < α) (ha : 0 < a)
    (hρ2 : 2 * ρ < 1)
    (ha1 : T * a ^ α < 1) :
    endpointRateFactor α T ρ a =
      (1 - T * a ^ α) * endpointEscapeFactor α ρ := by
  let q : ℝ := 1 - 2 * ρ
  let H : ℝ := 1 - T * a ^ α
  have hq : 0 < q := by dsimp [q]; linarith
  have hH : 0 < H := by dsimp [H]; linarith
  have hscale : endpointTailScale α T ρ a = q * a / H ^ (1 / α) := by
    simp [endpointTailScale, q, H]
  have hratio : a / endpointTailScale α T ρ a = H ^ (1 / α) / q := by
    rw [hscale]
    dsimp [q, H]
    field_simp [ha.ne', hq.ne']
  have hpow : (H ^ (1 / α) / q) ^ α = H / (q ^ α) := by
    rw [Real.div_rpow (le_of_lt (Real.rpow_pos_of_pos hH _)) hq.le]
    have hexp : (1 / α) * α = 1 := by field_simp [hα.ne']
    rw [← Real.rpow_mul hH.le, hexp, Real.rpow_one]
  rw [endpointRateFactor, hratio, hpow]
  dsimp [H, q, endpointEscapeFactor]
  have hρ1' : 1 - ρ ≠ 0 := ne_of_gt (by linarith)
  have hqpow : q ^ α ≠ 0 := (Real.rpow_pos_of_pos hq α).ne'
  field_simp [hρ1', hqpow]

private theorem tendsto_endpointRateFactor
    {α T ρ : ℝ} (hα : 0 < α) (hρ2 : 2 * ρ < 1) :
    Tendsto (endpointRateFactor α T ρ) (𝓝[>] (0 : ℝ))
      (𝓝 (endpointEscapeFactor α ρ)) := by
  let l := 𝓝[>] (0 : ℝ)
  have hpow : Tendsto (fun a : ℝ => a ^ α) l (𝓝 0) := by
    have hcont := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
    simpa [Real.zero_rpow hα.ne'] using
      (hcont.mono_left (nhdsWithin_le_nhds : l ≤ 𝓝 0))
  have hcut : Tendsto (fun a : ℝ => T * a ^ α) l (𝓝 0) := by
    simpa using hpow.const_mul T
  have hsmall : ∀ᶠ a : ℝ in l, T * a ^ α < 1 :=
    hcut.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hfactorEq : endpointRateFactor α T ρ =ᶠ[l]
      fun a : ℝ => (1 - T * a ^ α) * endpointEscapeFactor α ρ := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with a ha ha1
    exact endpointRateFactor_eq hα ha hρ2 ha1
  have hfactor : Tendsto
      (fun a : ℝ => (1 - T * a ^ α) * endpointEscapeFactor α ρ) l
      (𝓝 (endpointEscapeFactor α ρ)) := by
    have hH : Tendsto (fun a : ℝ => 1 - T * a ^ α) l (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hcut
    simpa using hH.mul_const (endpointEscapeFactor α ρ)
  exact Filter.Tendsto.congr' hfactorEq.symm hfactor

private theorem tendsto_endpointEscapeFactor
    {α : ℝ} :
    Tendsto (endpointEscapeFactor α) (𝓝 (0 : ℝ)) (𝓝 1) := by
  have htwice : Tendsto (fun ρ : ℝ => 2 * ρ) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul tendsto_id :
      Tendsto (fun ρ : ℝ => (2 : ℝ) * ρ) (𝓝 0) (𝓝 ((2 : ℝ) * 0)))
  have hbase : Tendsto (fun ρ : ℝ => 1 - 2 * ρ) (𝓝 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub htwice
  have hpow : Tendsto (fun ρ : ℝ => (1 - 2 * ρ) ^ α)
      (𝓝 0) (𝓝 1) := by
    have hcont := (Real.continuousAt_rpow_const 1 α
      (Or.inl (by norm_num : (1 : ℝ) ≠ 0))).tendsto
    simpa only [Function.comp_def, Real.one_rpow] using hcont.comp hbase
  have hlinear : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_id : Tendsto id (𝓝 0) (𝓝 (0 : ℝ)))
  have hdenom : Tendsto (fun ρ : ℝ => (1 - 2 * ρ) ^ α * (1 - ρ))
      (𝓝 0) (𝓝 1) := by
    simpa using hpow.mul hlinear
  have hpowInv := hpow.inv₀ one_ne_zero
  have hlinearInv := hlinear.inv₀ one_ne_zero
  have hprod := hlinearInv.mul hpowInv
  change Tendsto (fun ρ : ℝ =>
    (1 - ρ)⁻¹ * ((1 - 2 * ρ) ^ α)⁻¹) (𝓝 0) (𝓝 1)
  simpa using hprod

private theorem eventually_endpointComparisonProbability_pos
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {C : ℝ} (hC : C < 0)
    (hcenter : Tendsto (stableCenteredLogRate P X α)
      (𝓝[>] (0 : ℝ)) (𝓝 C))
    (c b ε δ : ℝ) (hc : -1 ≤ c) (hcb : c < b) (hb : b ≤ 1)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
      0 < (centeredEndpointComparisonProbability P X ε c b a).toReal ∧
        Real.log ((centeredCorridorProbability P X a).toReal) / (1 - δ) ≤
          Real.log ((centeredEndpointComparisonProbability P X ε c b a).toReal) := by
  let l := 𝓝[>] (0 : ℝ)
  have hratio := h.eventually_one_sub_le_log_corridor_div_endpointCorridor_of_cdf
    hcdf c b ε δ hc hcb hb hε hδ
  have hcenterNeg : ∀ᶠ a : ℝ in l,
      stableCenteredLogRate P X α a < 0 :=
    hcenter.eventually (Iio_mem_nhds hC)
  filter_upwards [self_mem_nhdsWithin, hratio, hcenterNeg] with a ha hrat hneg
  have hqlog : Real.log ((centeredCorridorProbability P X a).toReal) < 0 := by
    have hmul : a ^ α *
        Real.log ((centeredCorridorProbability P X a).toReal) < 0 := by
      simpa [stableCenteredLogRate] using hneg
    have hp : 0 < a ^ α := Real.rpow_pos_of_pos ha α
    by_contra hnot
    have hnonneg : 0 ≤ Real.log ((centeredCorridorProbability P X a).toReal) :=
      le_of_not_gt hnot
    have := mul_nonneg hp.le hnonneg
    linarith
  have hlogs := endpoint_log_bound_of_ratio hδ1 hqlog hrat
  exact ⟨hlogs.1, hlogs.2.2⟩

private theorem exists_shiftedEndpointEntrance
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {d ρ : ℝ} (hd : -1 < d ∧ d < 1) (hρ : 0 < ρ) :
    ∃ T : ℝ≥0, 0 < T ∧
      0 < P (fullSegmentCorridorReturnEvent X 0 T
        (d - 1) (d + 1) (d - ρ) (d + ρ)) := by
  exact h.exists_pos_time_measure_fullSegmentCorridorReturnEvent_pos
    (d - 1) (d + 1) d ρ
    (by linarith [hd.2]) (by linarith [hd.1])
    (by linarith) (by linarith) hρ hcdf

private theorem eventually_shiftedEndpointProbability_pos_of_fixed_window
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {C d c b ρ : ℝ} (hC : C < 0)
    (hcenter : Tendsto (stableCenteredLogRate P X α)
      (𝓝[>] (0 : ℝ)) (𝓝 C))
    (hd : -1 < d ∧ d < 1) (hc : -1 < c) (hb : b ≤ 1)
    (hρ : 0 < ρ) (hρ2 : 2 * ρ < 1)
    (hρgap : 4 * ρ < b - c) :
    ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
      0 < (shiftedEndpointCorridorProbability P X d c b a).toReal := by
  let c₀ := (c + 2 * ρ) / (1 - 2 * ρ)
  let b₀ := (b - 2 * ρ) / (1 - 2 * ρ)
  have hq : 0 < 1 - 2 * ρ := by linarith
  have hc₀ : -1 ≤ c₀ := by
    dsimp [c₀]
    rw [le_div_iff₀ hq]
    nlinarith
  have hc₀b₀ : c₀ < b₀ := by
    dsimp [c₀, b₀]
    apply div_lt_div_of_pos_right _ hq
    nlinarith [hρgap]
  have hb₀ : b₀ ≤ 1 := by
    dsimp [b₀]
    rw [div_le_one hq]
    linarith [hb]
  have hα : 0 < α := h.increments.strictlyStable.1
  obtain ⟨T, hT, hentrance⟩ := exists_shiftedEndpointEntrance h hcdf hd hρ
  have htail := tendsto_endpointTailScale (T := (T : ℝ)) hα hρ2
  have hρltOne : ρ < 1 := by linarith [hρ2]
  have hcomparison :=
    htail.eventually
      (eventually_endpointComparisonProbability_pos h hcdf hC hcenter
        c₀ b₀ ρ ρ hc₀ hc₀b₀ hb₀ hρ hρ hρltOne)
  have hglue := eventually_shiftedEndpoint_ge_fixedEntrance_mul_endpointComparison
    h d c b ρ hc hb hρ hρgap T hT
  have hpReal : 0 <
      (P (fullSegmentCorridorReturnEvent X 0 T
        (d - 1) (d + 1) (d - ρ) (d + ρ))).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hentrance, measure_lt_top P _⟩
  filter_upwards [hcomparison, hglue] with a hE hbound
  have hFReal :
      (P (fullSegmentCorridorReturnEvent X 0 T
        (d - 1) (d + 1) (d - ρ) (d + ρ))).toReal *
        (centeredEndpointComparisonProbability P X ρ c₀ b₀
          (endpointTailScale α (T : ℝ) ρ a)).toReal ≤
      (shiftedEndpointCorridorProbability P X d c b a).toReal := by
    rw [← ENNReal.toReal_mul]
    exact (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top (measure_lt_top P _).ne (measure_lt_top P _).ne)
      (measure_lt_top P _).ne).mpr hbound
  exact lt_of_lt_of_le (mul_pos hpReal hE.1) hFReal

/-- The terminal-window corridor has the same finite negative escape rate as
the range tube, centered corridor, and translated corridor. The event keeps
the source's exact left-open, right-closed endpoint convention. -/
theorem IsStableLevyProcess.exists_shiftedEndpointCorridor_escape_rate
    {Ω : Type*} [MeasurableSpace Ω]
    {α d c b : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hd : -1 < d ∧ d < 1) (hc : -1 < c) (hcb : c < b) (hb : b ≤ 1) :
    ∃ C : ℝ, C < 0 ∧
      Tendsto (stableRangeLogRate P X α)
        (𝓝[>] (0 : ℝ)) (𝓝 C) ∧
      Tendsto (stableCenteredLogRate P X α)
        (𝓝[>] (0 : ℝ)) (𝓝 C) ∧
      Tendsto (stableShiftedCorridorLogRate P X α d)
        (𝓝[>] (0 : ℝ)) (𝓝 C) ∧
      Tendsto (stableShiftedEndpointCorridorLogRate P X α d c b)
        (𝓝[>] (0 : ℝ)) (𝓝 C) := by
  obtain ⟨C, hC, hRange, hcenter, hshift⟩ :=
    h.exists_shiftedCorridor_escape_rate hcdf hd
  let l : Filter ℝ := 𝓝[>] (0 : ℝ)
  have hα : 0 < α := h.increments.strictlyStable.1
  let endpointRate := stableShiftedEndpointCorridorLogRate P X α d c b
  have hendpoint : Tendsto endpointRate l (𝓝 C) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro x hx
      have htarget : 1 < x / C := (lt_div_iff_of_neg hC).2 (by linarith)
      have hfactorLimit := tendsto_endpointEscapeFactor (α := α)
      have hfactorLimit' := hfactorLimit.mono_left
        (nhdsWithin_le_nhds : l ≤ 𝓝 (0 : ℝ))
      have hfactorEvent : ∀ᶠ ρ : ℝ in l,
          endpointEscapeFactor α ρ < x / C :=
        hfactorLimit'.eventually (Iio_mem_nhds htarget)
      have hgap : 0 < b - c := by linarith
      have hid : Tendsto id l (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_left (nhdsWithin_le_nhds : l ≤ 𝓝 (0 : ℝ))
      have hfour : Tendsto (fun ρ : ℝ => 4 * ρ) l (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul hid :
          Tendsto (fun ρ : ℝ => (4 : ℝ) * ρ) l (𝓝 ((4 : ℝ) * 0)))
      have hsmall : ∀ᶠ ρ : ℝ in l, 4 * ρ < min 1 (b - c) :=
        hfour.eventually (Iio_mem_nhds (lt_min (by norm_num) hgap))
      obtain ⟨ρ, ⟨hfactorSmall, hsmall⟩, hρ⟩ :=
        (hfactorEvent.and hsmall).and self_mem_nhdsWithin |>.exists
      have hρ1 : ρ < 1 := by
        have := lt_of_lt_of_le hsmall (min_le_left _ _)
        linarith
      have hρ2 : 2 * ρ < 1 := by
        have := lt_of_lt_of_le hsmall (min_le_left _ _)
        linarith
      have hρgap : 4 * ρ < b - c :=
        lt_of_lt_of_le hsmall (min_le_right _ _)
      have hfactorC : x < endpointEscapeFactor α ρ * C := by
        have hm := mul_lt_mul_of_neg_right hfactorSmall hC
        have hcancel : (x / C) * C = x := div_mul_cancel₀ x (ne_of_lt hC)
        linarith
      let c₀ : ℝ := (c + 2 * ρ) / (1 - 2 * ρ)
      let b₀ : ℝ := (b - 2 * ρ) / (1 - 2 * ρ)
      have hq : 0 < 1 - 2 * ρ := by linarith
      have hc₀ : -1 ≤ c₀ := by
        dsimp [c₀]
        rw [le_div_iff₀ hq]
        nlinarith [hc]
      have hc₀b₀ : c₀ < b₀ := by
        dsimp [c₀, b₀]
        apply div_lt_div_of_pos_right _ hq
        nlinarith [hρgap, hcb]
      have hb₀ : b₀ ≤ 1 := by
        dsimp [b₀]
        rw [div_le_one hq]
        linarith [hb]
      obtain ⟨T, hT, hentrance⟩ := exists_shiftedEndpointEntrance h hcdf hd hρ
      let p : ℝ≥0∞ := P (fullSegmentCorridorReturnEvent X 0 T
        (d - 1) (d + 1) (d - ρ) (d + ρ))
      have hp : 0 < p := by simpa [p] using hentrance
      have hpReal : 0 < p.toReal :=
        ENNReal.toReal_pos_iff.mpr ⟨hp, measure_lt_top P _⟩
      have htail := tendsto_endpointTailScale (T := (T : ℝ)) hα hρ2
      have hρltOne : ρ < 1 := by linarith [hρ2]
      have hEevent := htail.eventually
        (eventually_endpointComparisonProbability_pos h hcdf hC hcenter
          c₀ b₀ ρ ρ hc₀ hc₀b₀ hb₀ hρ hρ hρltOne)
      have hglue := eventually_shiftedEndpoint_ge_fixedEntrance_mul_endpointComparison
        h d c b ρ hc hb hρ hρgap T hT
      have hcenterTail : Tendsto
          (fun a : ℝ => stableCenteredLogRate P X α
            (endpointTailScale α (T : ℝ) ρ a)) l (𝓝 C) := hcenter.comp htail
      have hfactorTail := tendsto_endpointRateFactor (T := (T : ℝ)) hα hρ2
      have hproduct : Tendsto
          (fun a : ℝ => endpointRateFactor α (T : ℝ) ρ a *
            stableCenteredLogRate P X α (endpointTailScale α (T : ℝ) ρ a))
          l (𝓝 (endpointEscapeFactor α ρ * C)) := hfactorTail.mul hcenterTail
      have hpower : Tendsto (fun a : ℝ => a ^ α) l (𝓝 0) := by
        have hcont := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
        simpa [Real.zero_rpow hα.ne'] using
          (hcont.mono_left (nhdsWithin_le_nhds : l ≤ 𝓝 0))
      have hcorrection : Tendsto
          (fun a : ℝ => a ^ α * Real.log p.toReal) l (𝓝 0) := by
        simpa using hpower.mul_const (Real.log p.toReal)
      have hcut : Tendsto (fun a : ℝ => (T : ℝ) * a ^ α) l (𝓝 0) := by
        simpa using hpower.const_mul (T : ℝ)
      have hpowerSmall : ∀ᶠ a : ℝ in l, (T : ℝ) * a ^ α < 1 :=
        hcut.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
      have hlower : Tendsto
          (fun a : ℝ => a ^ α * Real.log p.toReal +
            endpointRateFactor α (T : ℝ) ρ a *
              stableCenteredLogRate P X α (endpointTailScale α (T : ℝ) ρ a))
          l (𝓝 (endpointEscapeFactor α ρ * C)) := by
        simpa using hcorrection.add hproduct
      have hlowerEventually := hlower.eventually (Ioi_mem_nhds hfactorC)
      have hpointwise : ∀ᶠ a : ℝ in l,
          a ^ α * Real.log p.toReal +
              endpointRateFactor α (T : ℝ) ρ a *
                stableCenteredLogRate P X α (endpointTailScale α (T : ℝ) ρ a) ≤
            endpointRate a := by
        filter_upwards [self_mem_nhdsWithin, hglue, hEevent, hpowerSmall]
          with a ha hbound hE haSmall
        let s := endpointTailScale α (T : ℝ) ρ a
        have hspos : 0 < s := by
          dsimp [s, endpointTailScale]
          apply div_pos
          · exact mul_pos (by linarith [hρ2]) ha
          · apply Real.rpow_pos_of_pos
            have hbase : 0 < 1 - (T : ℝ) * a ^ α := by linarith
            simpa using hbase
        have hpfirst : p *
            centeredEndpointComparisonProbability P X ρ c₀ b₀ s ≤
            shiftedEndpointCorridorProbability P X d c b a := by
          simpa [p, s, endpointTailScale] using hbound
        have hpreal : 0 < p.toReal := hpReal
        have hmulReal : p.toReal *
            (centeredEndpointComparisonProbability P X ρ c₀ b₀ s).toReal ≤
            (shiftedEndpointCorridorProbability P X d c b a).toReal := by
          rw [← ENNReal.toReal_mul]
          exact (ENNReal.toReal_le_toReal
            (ENNReal.mul_ne_top (measure_lt_top P _).ne (measure_lt_top P _).ne)
            (measure_lt_top P _).ne).mpr hpfirst
        have hlog := Real.log_le_log (mul_pos hpreal hE.1) hmulReal
        rw [Real.log_mul hpreal.ne' hE.1.ne'] at hlog
        have hlogLower : Real.log p.toReal +
            Real.log ((centeredCorridorProbability P X s).toReal) / (1 - ρ) ≤
            Real.log ((shiftedEndpointCorridorProbability P X d c b a).toReal) := by
          linarith [hE.2, hlog]
        have hsPow : (a / s) ^ α * s ^ α = a ^ α := by
          rw [Real.div_rpow ha.le hspos.le]
          field_simp [(Real.rpow_pos_of_pos hspos α).ne']
        have hfactorEq : endpointRateFactor α (T : ℝ) ρ a *
              stableCenteredLogRate P X α s =
            a ^ α *
              (Real.log ((centeredCorridorProbability P X s).toReal) /
                (1 - ρ)) := by
          unfold endpointRateFactor stableCenteredLogRate
          dsimp [s]
          calc
            ((a / endpointTailScale α (T : ℝ) ρ a) ^ α / (1 - ρ)) *
                (endpointTailScale α (T : ℝ) ρ a ^ α *
                  Real.log ((centeredCorridorProbability P X
                    (endpointTailScale α (T : ℝ) ρ a)).toReal)) =
              (((a / endpointTailScale α (T : ℝ) ρ a) ^ α) *
                endpointTailScale α (T : ℝ) ρ a ^ α) / (1 - ρ) *
                  Real.log ((centeredCorridorProbability P X
                    (endpointTailScale α (T : ℝ) ρ a)).toReal) := by ring
            _ = a ^ α / (1 - ρ) *
                Real.log ((centeredCorridorProbability P X
                  (endpointTailScale α (T : ℝ) ρ a)).toReal) := by
                  rw [hsPow]
            _ = a ^ α *
                (Real.log ((centeredCorridorProbability P X
                  (endpointTailScale α (T : ℝ) ρ a)).toReal) / (1 - ρ)) := by ring
        have hsum := mul_le_mul_of_nonneg_left hlogLower
          (Real.rpow_nonneg ha.le α)
        have hsumEq : a ^ α *
            (Real.log p.toReal +
              Real.log ((centeredCorridorProbability P X s).toReal) /
                (1 - ρ)) =
            a ^ α * Real.log p.toReal +
              endpointRateFactor α (T : ℝ) ρ a * stableCenteredLogRate P X α s := by
          calc
            _ = a ^ α * Real.log p.toReal +
                a ^ α *
                  (Real.log ((centeredCorridorProbability P X s).toReal) /
                    (1 - ρ)) := by ring
            _ = _ := by rw [← hfactorEq]
        dsimp [endpointRate]
        rw [← hsumEq]
        exact hsum
      filter_upwards [hlowerEventually, hpointwise] with a hlt hle
      exact lt_of_lt_of_le hlt hle
    · intro x hx
      let ρ : ℝ := min (1 / 8) ((b - c) / 8)
      have hgap : 0 < b - c := by linarith
      have hρ : 0 < ρ := by
        dsimp [ρ]
        exact lt_min (by norm_num) (by positivity)
      have hρlt : ρ ≤ 1 / 8 := min_le_left _ _
      have hρgap : ρ ≤ (b - c) / 8 := min_le_right _ _
      have hρ1 : ρ < 1 := by linarith
      have hρ2 : 2 * ρ < 1 := by linarith
      have hρgap4 : 4 * ρ < b - c := by nlinarith
      have hpos := eventually_shiftedEndpointProbability_pos_of_fixed_window
        h hcdf hC hcenter hd hc hb hρ hρ2 hρgap4
      have hupper : ∀ᶠ a : ℝ in l,
          endpointRate a ≤ stableShiftedCorridorLogRate P X α d a := by
        filter_upwards [self_mem_nhdsWithin, hpos] with a ha hprobPos
        have hprobSubset :
            shiftedEndpointCorridorProbability P X d c b a ≤
              shiftedCorridorProbability P X d a := by
          change P (fullSegmentCorridorIocReturnEvent X 0 1
            (a * (d - 1)) (a * (d + 1))
            (a * (d + c)) (a * (d + b))) ≤ _
          apply measure_mono
          intro ω hω
          exact hω.1
        have hprobReal :
            (shiftedEndpointCorridorProbability P X d c b a).toReal ≤
              (shiftedCorridorProbability P X d a).toReal :=
          (ENNReal.toReal_le_toReal (measure_lt_top P _).ne
            (measure_lt_top P _).ne).mpr hprobSubset
        have hlog := Real.log_le_log hprobPos hprobReal
        have hscaled := mul_le_mul_of_nonneg_left hlog
          (Real.rpow_nonneg ha.le α)
        simpa [endpointRate, stableShiftedEndpointCorridorLogRate,
          stableShiftedCorridorLogRate] using hscaled
      have hshiftEventually : ∀ᶠ a : ℝ in l,
          stableShiftedCorridorLogRate P X α d a < x :=
        hshift.eventually (Iio_mem_nhds hx)
      filter_upwards [hupper, hshiftEventually] with a hle hlt
      exact lt_of_le_of_lt hle hlt
  exact ⟨C, hC, by simpa [l] using hRange,
    by simpa [l] using hcenter, by simpa [l] using hshift,
    by simpa [endpointRate, l] using hendpoint⟩

/-- The terminal-window event has the same logarithmic asymptotic as the
translated corridor. This is relation (20); the endpoint interval remains
left-open and right-closed in the defining probability. -/
theorem IsStableLevyProcess.tendsto_log_shiftedEndpointCorridor_div_log_shiftedCorridor
    {Ω : Type*} [MeasurableSpace Ω]
    {α d c b : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hd : -1 < d ∧ d < 1) (hc : -1 < c) (hcb : c < b) (hb : b ≤ 1) :
    Tendsto
      (fun a : ℝ =>
        Real.log ((shiftedEndpointCorridorProbability P X d c b a).toReal) /
          Real.log ((shiftedCorridorProbability P X d a).toReal))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  obtain ⟨C, hC, _, _, hshift, hendpoint⟩ :=
    h.exists_shiftedEndpointCorridor_escape_rate hcdf hd hc hcb hb
  have hratio := hendpoint.div hshift (ne_of_lt hC)
  have hcancel :
      (fun a : ℝ => stableShiftedEndpointCorridorLogRate P X α d c b a /
        stableShiftedCorridorLogRate P X α d a) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun a : ℝ =>
        Real.log ((shiftedEndpointCorridorProbability P X d c b a).toReal) /
          Real.log ((shiftedCorridorProbability P X d a).toReal)) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have haPow : a ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha α)
    simpa [stableShiftedEndpointCorridorLogRate,
      stableShiftedCorridorLogRate] using
      (mul_div_mul_left
        (Real.log ((shiftedEndpointCorridorProbability P X d c b a).toReal))
        (Real.log ((shiftedCorridorProbability P X d a).toReal)) haPow)
  simpa [div_self (ne_of_lt hC)] using hratio.congr' hcancel

/-- The endpoint-constrained corridor rate uses the same constant as the
centered range rate. The source endpoint comparison proves the rate for some
constant; uniqueness of limits identifies it with the supplied base rate. -/
theorem IsStableLevyProcess.tendsto_shiftedEndpointCorridorLogRate_of_tendsto_stableRangeLogRate
    {Ω : Type*} [MeasurableSpace Ω]
    {α C d c₀ b₀ : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hbase : Tendsto (stableRangeLogRate P X α)
      (𝓝[>] (0 : ℝ)) (𝓝 C))
    (hd : -1 < d ∧ d < 1) (hc : -1 < c₀) (hcb : c₀ < b₀)
    (hb : b₀ ≤ 1) :
    Tendsto (stableShiftedEndpointCorridorLogRate P X α d c₀ b₀)
      (𝓝[>] (0 : ℝ)) (𝓝 C) := by
  obtain ⟨C', _, hrange, _, _, hendpoint⟩ :=
    h.exists_shiftedEndpointCorridor_escape_rate hcdf hd hc hcb hb
  have hC : C' = C := tendsto_nhds_unique hrange hbase
  simpa [hC] using hendpoint

/-- A fixed relative endpoint corridor has the same small-width rate after
the stable spatial rescaling `a = radius / c`. This is the endpoint-window
version of the escape-rate rescaling used for one-block lower bounds. -/
theorem IsStableLevyProcess.tendsto_inv_rpow_mul_log_shiftedEndpointCorridorProbability
    {Ω : Type*} [MeasurableSpace Ω]
    {α d c₀ b₀ : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {C : ℝ} (hbase : Tendsto (stableRangeLogRate P X α)
      (𝓝[>] (0 : ℝ)) (𝓝 C))
    (hd : -1 < d ∧ d < 1) (hc : -1 < c₀) (hcb : c₀ < b₀)
    (hb : b₀ ≤ 1) {radius : ℝ} (hradius : 0 < radius) :
    Tendsto
        (fun scale : ℝ => scale⁻¹ ^ α * Real.log
          ((shiftedEndpointCorridorProbability P X d c₀ b₀
            (radius / scale)).toReal))
        atTop (𝓝 (C / radius ^ α)) := by
  have hendpoint :=
    h.tendsto_shiftedEndpointCorridorLogRate_of_tendsto_stableRangeLogRate
      hcdf hbase hd hc hcb hb
  let l : Filter ℝ := 𝓝[>] (0 : ℝ)
  have hzero : Tendsto (fun scale : ℝ => radius / scale) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun scale : ℝ => radius * scale⁻¹) atTop
          (𝓝 (radius * (0 : ℝ))))
  have hpos : ∀ᶠ scale : ℝ in atTop, 0 < radius / scale := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with scale hscale
    exact div_pos hradius hscale
  have hwithin : Tendsto (fun scale : ℝ => radius / scale) atTop l :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  have hendpoint' := hendpoint.comp hwithin
  have hquot : Tendsto
      (fun scale : ℝ =>
        stableShiftedEndpointCorridorLogRate P X α d c₀ b₀
          (radius / scale) / radius ^ α)
      atTop (𝓝 (C / radius ^ α)) := by
    simpa [div_eq_mul_inv] using hendpoint'.div_const (radius ^ α)
  have heq : (fun scale : ℝ => scale⁻¹ ^ α * Real.log
      ((shiftedEndpointCorridorProbability P X d c₀ b₀
        (radius / scale)).toReal)) =ᶠ[atTop]
      fun scale : ℝ =>
        stableShiftedEndpointCorridorLogRate P X α d c₀ b₀
          (radius / scale) / radius ^ α := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with scale hscale
    have hdiv : (radius / scale) ^ α = radius ^ α / scale ^ α :=
      Real.div_rpow hradius.le hscale.le α
    have hinv : scale⁻¹ ^ α = (scale ^ α)⁻¹ :=
      Real.inv_rpow hscale.le α
    have hrpow : radius ^ α ≠ 0 := (Real.rpow_pos_of_pos hradius α).ne'
    have hscalePow : scale ^ α ≠ 0 := (Real.rpow_pos_of_pos hscale α).ne'
    change scale⁻¹ ^ α * Real.log
        ((shiftedEndpointCorridorProbability P X d c₀ b₀
          (radius / scale)).toReal) =
      ((radius / scale) ^ α * Real.log
        ((shiftedEndpointCorridorProbability P X d c₀ b₀
          (radius / scale)).toReal)) / radius ^ α
    rw [hdiv, hinv]
    field_simp
  exact hquot.congr' heq.symm

end ProbabilityTheory

end

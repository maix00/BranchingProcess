/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.CharacteristicFunction.Tauberian.FrequencyAverageLimit
public import Probability.Distributions.CharacteristicFunction.Symmetrization.Tail
public import Probability.Distributions.Stable.Attraction.Normal

/-!
# Characteristic-defect tails in the normal domain of attraction

Gaussian attraction makes the squared-modulus defect regularly varying with
index two. The frequency-averaged Tauberian estimate therefore gives a
little-o tail bound for the symmetrized increment law, without a moment
assumption.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- In the standard Gaussian domain of attraction, the closed tail of the
symmetrized increment law is little-o of the squared-modulus characteristic
defect. The tail here is for `X - X'`, where `X'` is an independent copy; this
does not assert the corresponding truncated-moment or Feller condition for
the original increment law. -/
theorem IsInDomainOfAttractionAlong.tendsto_symmetrizedClosedAbsTail_div_normDefect_atTop_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    Tendsto
      (fun x : ℝ => (symmetrizedMeasure ν).real
        {y : ℝ | x ≤ |y|} /
          (1 - ‖charFun ν (x⁻¹)‖ ^ 2))
      atTop (nhds 0) := by
  let hlimit : IsAlphaStable 2 (gaussianReal 0 1) :=
    (isStrictlyAlphaStable_gaussianReal_zero (by norm_num)).isAlphaStable
  have hpos := h.eventually_pos_normDefect_nhdsGT_zero hlimit
  have hratio := h.tendstoUniformlyOn_normDefect_ratio_nhdsGT_zero hlimit
  have hratioNat : TendstoUniformlyOn
      (fun u t => (1 - ‖charFun ν (t * u)‖ ^ 2) /
        (1 - ‖charFun ν u‖ ^ 2))
      (fun t => t ^ (2 : ℕ)) (𝓝[>] (0 : ℝ)) (Set.Icc 1 2) := by
    exact hratio.congr_right (fun t _ => Real.rpow_natCast t 2)
  exact tendsto_symmetrizedClosedAbsTail_div_normDefect_atTop ν hpos hratioNat

/-- In the standard Gaussian domain of attraction, the original increment
law also has a closed-tail little-o bound relative to its squared-modulus
characteristic defect. This transfers the symmetrized estimate through the
law of `X-X'` using the elementary two-sided-tail comparison. It is still
weaker than Feller's condition, whose denominator is the truncated second
moment. -/
theorem IsInDomainOfAttractionAlong.tendsto_closedAbsTail_div_normDefect_atTop_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    Tendsto
      (fun x : ℝ => ν.real {y : ℝ | x ≤ |y|} /
        (1 - ‖charFun ν (x⁻¹)‖ ^ 2))
      atTop (nhds 0) := by
  let D : ℝ → ℝ := fun x => 1 - ‖charFun ν (x⁻¹)‖ ^ 2
  let T : ℝ → ℝ := fun x => ν.real {y : ℝ | x ≤ |y|}
  let S : ℝ → ℝ := fun x => (symmetrizedMeasure ν).real
    {y : ℝ | x ≤ |y|}
  let hlimit : IsAlphaStable 2 (gaussianReal 0 1) :=
    (isStrictlyAlphaStable_gaussianReal_zero (by norm_num)).isAlphaStable
  have hpos := h.eventually_pos_normDefect_nhdsGT_zero hlimit
  have hsymm := h.tendsto_symmetrizedClosedAbsTail_div_normDefect_atTop_of_gaussian
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_inv_atTop_nhdsGT_zero
  have hDpos : ∀ᶠ x : ℝ in atTop, 0 < D x := by
    simpa [D] using hinv.eventually hpos
  have hquarterTop : Tendsto (fun x : ℝ => x / 4) atTop atTop := by
    have h := tendsto_id.const_mul_atTop
      (by norm_num : (0 : ℝ) < 1 / 4)
    have heq : (fun x : ℝ => (1 / 4 : ℝ) * x) = fun x => x / 4 := by
      funext x
      ring
    exact h.congr' (Filter.EventuallyEq.of_eq heq)
  have hquarterInv : Tendsto (fun x : ℝ => (x / 4)⁻¹)
      atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_inv_atTop_nhdsGT_zero.comp hquarterTop
  have hDquarterPos : ∀ᶠ x : ℝ in atTop, 0 < D (x / 4) := by
    simpa [D] using hquarterInv.eventually hpos
  have hratio4 : Tendsto
      (fun u : ℝ => (1 - ‖charFun ν (4 * u)‖ ^ 2) /
        (1 - ‖charFun ν u‖ ^ 2))
      (𝓝[>] (0 : ℝ)) (nhds 16) := by
    have hratio := h.tendsto_normDefect_ratio_nhdsGT_zero hlimit
      (4 : ℝ) (by norm_num)
    convert hratio using 1
    norm_num
  have hDscale : Tendsto (fun x : ℝ => D (x / 4) / D x)
      atTop (nhds 16) := by
    have h := hratio4.comp hinv
    have heq : (fun x : ℝ =>
        (1 - ‖charFun ν (4 * x⁻¹)‖ ^ 2) /
          (1 - ‖charFun ν (x⁻¹)‖ ^ 2)) =ᶠ[atTop]
        fun x => D (x / 4) / D x := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hinv4 : (x / 4)⁻¹ = 4 * x⁻¹ := by
        field_simp
      simp only [D, hinv4]
    exact h.congr' heq
  have hsymmQuarter : Tendsto (fun x : ℝ => S (x / 4) / D (x / 4))
      atTop (nhds 0) := by
    have h := hsymm.comp hquarterTop
    exact h.congr' (Filter.Eventually.of_forall fun _ => rfl)
  have hball : Tendsto (fun x : ℝ => absBallMass ν (x / 4))
      atTop (nhds 1) := by
    have htail := (twoSidedTail_tendsto_zero ν).comp hquarterTop
    have heq : (fun x : ℝ => absBallMass ν (x / 4)) =ᶠ[atTop]
        fun x => 1 - twoSidedTail ν (x / 4) := by
      filter_upwards [] with x
      exact absBallMass_eq_one_sub_twoSidedTail ν (x / 4)
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hbase : Tendsto (fun x : ℝ => (1 : ℝ) - twoSidedTail ν (x / 4))
        atTop (nhds (1 - 0)) := by
      simpa using hone.sub htail
    have hbase' : Tendsto (fun x : ℝ => 1 - twoSidedTail ν (x / 4))
        atTop (nhds 1) := by simpa using hbase
    exact hbase'.congr' heq.symm
  have hballHalf : ∀ᶠ x : ℝ in atTop,
      1 / 2 < ν.real {y : ℝ | |y| ≤ x / 4} := by
    have h := hball.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
    filter_upwards [h] with x hx
    simpa [absBallMass] using hx
  have hrawLe : ∀ᶠ x : ℝ in atTop, T x ≤ S (x / 4) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hballHalf] with x hx hmass
    have hrawSub : {y : ℝ | x ≤ |y|} ⊆ {y : ℝ | x / 2 < |y|} := by
      intro y hy
      change x / 2 < |y|
      exact lt_of_lt_of_le (by linarith) hy
    have hraw : T x ≤ twoSidedTail ν (x / 2) := by
      simpa [T, twoSidedTail] using
        (measureReal_mono (μ := ν) (s₁ := {y : ℝ | x ≤ |y|})
          (s₂ := {y : ℝ | x / 2 < |y|}) hrawSub)
    have hbase := twoSidedTail_symmetrized_lower_bound
      (μ := ν) (x := x / 4) (ε := 1) (by positivity) (by norm_num)
    have hbase' : 2 * twoSidedTail ν (x / 2) *
        ν.real {y : ℝ | |y| ≤ x / 4} ≤
        twoSidedTail (symmetrizedMeasure ν) (x / 4) := by
      have harg : (1 + (1 : ℝ)) * (x / 4) = x / 2 := by ring
      simpa [harg] using hbase
    have hcoef : 1 ≤ 2 * ν.real {y : ℝ | |y| ≤ x / 4} := by
      nlinarith
    have hstrictNonneg : 0 ≤ twoSidedTail ν (x / 2) :=
      measureReal_nonneg
    have hproduct : twoSidedTail ν (x / 2) ≤
        twoSidedTail (symmetrizedMeasure ν) (x / 4) := by
      calc
        twoSidedTail ν (x / 2) = twoSidedTail ν (x / 2) * 1 := by ring
        _ ≤ twoSidedTail ν (x / 2) *
              (2 * ν.real {y : ℝ | |y| ≤ x / 4}) :=
          mul_le_mul_of_nonneg_left hcoef hstrictNonneg
        _ = 2 * twoSidedTail ν (x / 2) *
              ν.real {y : ℝ | |y| ≤ x / 4} := by ring
        _ ≤ twoSidedTail (symmetrizedMeasure ν) (x / 4) := hbase'
    have hstrictToClosed : twoSidedTail (symmetrizedMeasure ν) (x / 4) ≤
        S (x / 4) := by
      apply measureReal_mono (μ := symmetrizedMeasure ν)
        (s₁ := {y : ℝ | x / 4 < |y|})
        (s₂ := {y : ℝ | x / 4 ≤ |y|})
      intro y hy
      change x / 4 < |y| at hy
      change x / 4 ≤ |y|
      exact le_of_lt hy
    calc
      T x ≤ twoSidedTail ν (x / 2) := hraw
      _ ≤ twoSidedTail (symmetrizedMeasure ν) (x / 4) := hproduct
      _ ≤ S (x / 4) := hstrictToClosed
  have hupper : Tendsto (fun x : ℝ => S (x / 4) / D x)
      atTop (nhds 0) := by
    have hprod := hsymmQuarter.mul hDscale
    have heq : (fun x : ℝ =>
        S (x / 4) / D (x / 4) * (D (x / 4) / D x)) =ᶠ[atTop]
        fun x => S (x / 4) / D x := by
      filter_upwards [hDquarterPos, hDpos] with x hq hD
      field_simp [ne_of_gt hq, ne_of_gt hD]
    simpa using hprod.congr' heq
  have hbound : ∀ᶠ x : ℝ in atTop,
      0 ≤ T x / D x ∧ T x / D x ≤ S (x / 4) / D x := by
    filter_upwards [hDpos, hrawLe] with x hD hle
    exact ⟨div_nonneg measureReal_nonneg hD.le,
      div_le_div_of_nonneg_right hle hD.le⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact hbound.mono fun x hx => hx.1
  · exact hbound.mono fun x hx => hx.2

end ProbabilityTheory

end

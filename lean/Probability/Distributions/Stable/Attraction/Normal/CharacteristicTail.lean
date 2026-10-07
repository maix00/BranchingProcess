/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.CharacteristicFunction.Tauberian.FrequencyAverageLimit
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

end ProbabilityTheory

end

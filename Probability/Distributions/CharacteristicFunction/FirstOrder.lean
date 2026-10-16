/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# First-order behavior of characteristic functions

The first derivative at zero is the mean. In particular, for an integrable
centered law the characteristic function differs from one by `o(t)`. This
first-order estimate is useful when comparing the real-part defect with the
squared-modulus defect without assuming a second moment.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- For an integrable centered law, the characteristic function has zero
first-order term at the origin. -/
theorem tendsto_mul_charFun_sub_one_of_integrable_id_of_integral_eq_zero
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun x : ℝ => x) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0) :
    Tendsto (fun t : ℝ => t * (charFun ν t⁻¹ - 1)) atTop (nhds 0) := by
  have hmem : MemLp (fun x : ℝ => x) (↑(1 : ℕ)) ν := by
    simpa only [Nat.cast_one] using (memLp_one_iff_integrable.mpr hint)
  have hcont : ContDiff ℝ 1 (charFun ν) := contDiff_charFun hmem
  have hdiff : DifferentiableAt ℝ (charFun ν) 0 :=
    hcont.differentiable (by norm_num) 0
  have hderivValue : deriv (charFun ν) 0 = 0 := by
    rw [← iteratedDeriv_one]
    rw [iteratedDeriv_charFun_zero hmem]
    simp [hmean]
  have hderiv : HasDerivAt (charFun ν) 0 0 := hdiff.hasDerivAt.congr_deriv hderivValue
  have hslope := hderiv.tendsto_slope_zero_right
  have hinv : Tendsto (fun t : ℝ => t⁻¹) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_inv_atTop_nhdsGT_zero
  have hcomp := hslope.comp hinv
  have heq : (fun t : ℝ =>
      (t⁻¹)⁻¹ • (charFun ν (0 + t⁻¹) - charFun ν 0)) =ᶠ[atTop]
      fun t => t * (charFun ν t⁻¹ - 1) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp
  exact hcomp.congr' heq

end ProbabilityTheory

end

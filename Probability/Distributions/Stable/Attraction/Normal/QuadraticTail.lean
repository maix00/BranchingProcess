/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.RegularVariation.Basic
public import Probability.Distributions.DomainOfAttraction.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Probability.Distributions.Moments.Truncated.Basic
public import Probability.Distributions.Stable.Attraction.Norming.Basic

import Probability.Distributions.CharacteristicFunction.TruncatedMoment
import Probability.Distributions.Stable.Attraction.Normal.Basic
import Probability.Distributions.Stable.Attraction.Normal.CharacteristicTail

/-!
# Quadratic tails in the Gaussian domain of attraction

Set `L^*(x)=∫_{|y|≤x}y²ν(dy)`. Gaussian attraction gives a negligible
quadratic tail, and the function `L^*` is slowly varying:

\[
\frac{x^2ν\{|y|>x\}}{L^*(x)}\longrightarrow0.
\]

## Public declarations

- `IsInDomainOfAttractionAlong.tendsto_secondTailRatio_of_gaussian` proves
  $x^2\nu\{|y|>x\}/L^*(x)\to0$.
- `IsInDomainOfAttractionAlong.eventually_pos_truncatedSecondMoment_of_gaussian`
  proves eventual positivity of $L^*$.
- `IsInDomainOfAttractionAlong.truncatedSecondMoment_isSlowlyVarying_of_gaussian`
  proves slow variation of $L^*(x)=\int_{|y|\le x}y^2\,d\nu$.
- `IsInDomainOfAttractionAlong.stableSlowVariation_two_isSlowlyVarying_of_gaussian`
  identifies the index-two stable factor with $L^*$ and proves it is slowly
  varying, including for infinite-variance laws.

The normal-domain characterization underlying these consequences is W. Feller,
*An Introduction to Probability Theory and Its Applications*, Vol. II, 2nd ed.
(Wiley, 1971), Section XVII.5, Theorem 2 (ISBN 978-0-471-25709-7).
-/

open Filter MeasureTheory Set
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

private lemma normDefect_le_truncatedSecondMoment_add_closedTail
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {x : ℝ} (hx : 0 < x) :
    1 - ‖charFun ν x⁻¹‖ ^ 2 ≤
      truncatedSecondMoment ν x / x ^ 2 +
        4 * ν.real {y : ℝ | x ≤ |y|} := by
  have hcosUpper := cosineDefectIntegral_upper_bound_truncatedSecondMoment_add_tail ν hx
  have hdefect : 1 - ‖charFun ν x⁻¹‖ ^ 2 ≤
      2 * cosineDefectIntegral ν x⁻¹ := by
    rw [cosineDefectIntegral_eq_one_sub_charFun_re]
    have hnorm := norm_charFun_le_one (μ := ν) (x⁻¹)
    have hre := Complex.re_le_norm (charFun ν x⁻¹)
    nlinarith
  have htailSub : {y : ℝ | x < |y|} ⊆ {y : ℝ | x ≤ |y|} := by
    intro y hy
    change x < |y| at hy
    exact le_of_lt hy
  have htail := measureReal_mono (μ := ν) htailSub (measure_ne_top ν _)
  calc
    1 - ‖charFun ν x⁻¹‖ ^ 2 ≤ 2 * cosineDefectIntegral ν x⁻¹ := hdefect
    _ ≤ 2 * (truncatedSecondMoment ν x / (2 * x ^ 2) +
          2 * ν.real {y : ℝ | x < |y|}) :=
      mul_le_mul_of_nonneg_left hcosUpper (by norm_num)
    _ = truncatedSecondMoment ν x / x ^ 2 +
          4 * ν.real {y : ℝ | x < |y|} := by field_simp [hx.ne']; ring
    _ ≤ truncatedSecondMoment ν x / x ^ 2 +
          4 * ν.real {y : ℝ | x ≤ |y|} :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left htail (by norm_num))

/-- Gaussian attraction forces the quadratic-tail condition, without a
finite variance assumption. The argument compares the cosine defect with the
truncated second moment and the closed tail, then uses the characteristic-tail
estimate. -/
private lemma gaussian_truncatedSecondMoment_data
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    (Tendsto
      (fun x : ℝ => x ^ 2 * ν.real {y : ℝ | x < |y|} /
        truncatedSecondMoment ν x) atTop (nhds 0)) ∧
      (∀ᶠ x : ℝ in atTop, 0 < truncatedSecondMoment ν x) := by
  let D : ℝ → ℝ := fun x => 1 - ‖charFun ν (x⁻¹)‖ ^ 2
  let T : ℝ → ℝ := fun x => ν.real {y : ℝ | x ≤ |y|}
  let V : ℝ → ℝ := truncatedSecondMoment ν
  have htail := h.tendsto_closedAbsTail_div_normDefect_atTop_of_gaussian
  have hDpos : ∀ᶠ x : ℝ in atTop, 0 < D x := by
    let hlimit : IsAlphaStable 2 (gaussianReal 0 1) :=
      (isStrictlyAlphaStable_gaussianReal_zero (by norm_num)).isAlphaStable
    have hpos := h.eventually_pos_normDefect_nhdsGT_zero hlimit
    exact tendsto_inv_atTop_nhdsGT_zero.eventually hpos
  have hsmall : ∀ᶠ x : ℝ in atTop, 4 * T x / D x ≤ 1 / 2 := by
    have h := htail.const_mul (4 : ℝ)
    have h' : Tendsto (fun x : ℝ => 4 * T x / D x) atTop (nhds 0) := by
      have hEq : (fun x : ℝ => 4 * (T x / D x)) =ᶠ[atTop]
          fun x => 4 * T x / D x := by
        filter_upwards [] with x
        ring
      simpa using h.congr' hEq
    filter_upwards [h'.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with x hx
    exact le_of_lt hx
  have hVpos : ∀ᶠ x : ℝ in atTop, 0 < V x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hDpos, hsmall] with x hx hDx hs
    have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
    have hineq := normDefect_le_truncatedSecondMoment_add_closedTail ν hx
    have hDt : D x ≤ V x / x ^ 2 + 4 * T x := by
      simpa [D, T, V] using hineq
    have htailSmall : 4 * T x ≤ D x / 2 := by
      have hs' := (div_le_iff₀ hDx).mp hs
      nlinarith
    have hVlower : D x / 2 ≤ V x / x ^ 2 := by linarith
    have hVratio : 0 < V x / x ^ 2 := lt_of_lt_of_le (div_pos hDx (by norm_num)) hVlower
    exact (div_pos_iff_of_pos_right hx2).mp hVratio
  have hbound : ∀ᶠ x : ℝ in atTop,
      0 ≤ x ^ 2 * ν.real {y : ℝ | x < |y|} / V x ∧
        x ^ 2 * ν.real {y : ℝ | x < |y|} / V x ≤ 2 * (T x / D x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hDpos, hVpos, hsmall]
      with x hx hDx hVx hs
    have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
    have hineq := normDefect_le_truncatedSecondMoment_add_closedTail ν hx
    have hDt : D x ≤ V x / x ^ 2 + 4 * T x := by
      simpa [D, T, V] using hineq
    have hsmall' : 4 * T x ≤ D x / 2 := by
      have hs' := (div_le_iff₀ hDx).mp hs
      nlinarith
    have hVratio : D x / 2 ≤ V x / x ^ 2 := by linarith
    have hVmul : x ^ 2 * D x ≤ 2 * V x := by
      have := (le_div_iff₀ hx2).mp hVratio
      nlinarith
    have htailOpen : 0 ≤ ν.real {y : ℝ | x < |y|} := measureReal_nonneg
    have htailClosed : 0 ≤ T x := measureReal_nonneg
    have htailLe : ν.real {y : ℝ | x < |y|} ≤ T x := by
      have hle := measureReal_mono (μ := ν)
        (s₁ := {y : ℝ | x < |y|}) (s₂ := {y : ℝ | x ≤ |y|})
        (by intro y hy; exact le_of_lt (by change x < |y| at hy; exact hy))
        (measure_ne_top ν _)
      simpa [T] using hle
    have hcross : x ^ 2 * ν.real {y : ℝ | x < |y|} * D x ≤
        2 * T x * V x := by
      calc
        x ^ 2 * ν.real {y : ℝ | x < |y|} * D x ≤ x ^ 2 * T x * D x := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left htailLe (sq_nonneg x)) hDx.le
        _ = T x * (x ^ 2 * D x) := by ring
        _ ≤ T x * (2 * V x) := by nlinarith [mul_le_mul_of_nonneg_left hVmul htailClosed]
        _ = 2 * T x * V x := by ring
    have hdiv : x ^ 2 * ν.real {y : ℝ | x < |y|} / V x ≤ 2 * (T x / D x) := by
      rw [div_le_iff₀ hVx, div_eq_mul_inv]
      calc
        x ^ 2 * ν.real {y : ℝ | x < |y|} ≤
            (2 * T x * V x) / D x := (le_div_iff₀ hDx).2 (by simpa [mul_assoc] using hcross)
        _ = 2 * (T x / D x) * V x := by field_simp
    exact ⟨div_nonneg (mul_nonneg (sq_nonneg x) htailOpen) hVx.le, hdiv⟩
  have hupper := htail.const_mul (2 : ℝ)
  have hupper' : Tendsto (fun x : ℝ => 2 * (T x / D x)) atTop (nhds 0) := by
    simpa [T, D, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hupper
  have hlimit := tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper'
    (hbound.mono fun x hx => hx.1)
    (hbound.mono fun x hx => hx.2)
  exact ⟨by simpa [V] using hlimit, hVpos⟩

/-- Gaussian attraction forces the quadratic-tail ratio condition, without a
finite variance assumption. This is the quadratic-tail consequence of the
normal-domain characterization in W. Feller, *An Introduction to Probability
Theory and Its Applications*, Vol. II, 2nd ed. (Wiley, 1971), Section XVII.5,
Theorem 2 (ISBN 978-0-471-25709-7). -/
theorem IsInDomainOfAttractionAlong.tendsto_secondTailRatio_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    Tendsto
      (fun x : ℝ => x ^ 2 * ν.real {y : ℝ | x < |y|} /
        truncatedSecondMoment ν x) atTop (nhds 0) :=
  (gaussian_truncatedSecondMoment_data h).1

/-- The truncated second moment is eventually positive in the normal domain
of attraction, including the infinite-variance case. -/
theorem IsInDomainOfAttractionAlong.eventually_pos_truncatedSecondMoment_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    ∀ᶠ x : ℝ in atTop, 0 < truncatedSecondMoment ν x :=
  (gaussian_truncatedSecondMoment_data h).2

/-- The truncated second moment is slowly varying throughout the normal
domain of attraction, including the infinite-variance case. -/
theorem IsInDomainOfAttractionAlong.truncatedSecondMoment_isSlowlyVarying_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    Asymptotics.IsSlowlyVaryingAtTop (truncatedSecondMoment ν) := by
  apply isSlowlyVarying_truncatedSecondMoment_of_tendsto_secondTailRatio ν
  · exact h.eventually_pos_truncatedSecondMoment_of_gaussian
  · exact h.tendsto_secondTailRatio_of_gaussian

/-- The Mogulskii factor `L*` at the normal endpoint is slowly varying for
every Gaussian domain of attraction, even when the increment law has infinite
variance. -/
theorem IsInDomainOfAttractionAlong.stableSlowVariation_two_isSlowlyVarying_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation 2 ν) := by
  rw [show stableSlowVariation 2 ν = truncatedSecondMoment ν by
    funext x
    exact stableSlowVariation_two ν x]
  exact h.truncatedSecondMoment_isSlowlyVarying_of_gaussian
end ProbabilityTheory

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Probability.Distributions.Stable.Attraction.Norming.Basic

/-!
# Stable norming at index two

Let `M₂=∫x²ν(dx)` be positive and finite. The canonical norming and its
asymptotic forms are

\[
B_n=\sqrt{nM_2},\qquad
\frac{B_n}{\sqrt n}\longrightarrow\sqrt{M_2},\qquad
\frac{B_n^2}{n}\longrightarrow M_2,
\qquad
\frac{nV_ν(B_n)}{B_n^2}\longrightarrow1,
\]

where `V_ν(u)=∫_{|x|≤u}x²ν(dx)`; the module also constructs `B` as an
index-two stable norming.

## Public declarations

* `isStableNorming_two_of_posSecondMoment` constructs the canonical
  norming $\sqrt{n\int x^2\,d\nu}$ from a positive finite second moment.
* `stableSlowVariation_two_isSlowlyVarying_of_posSecondMoment` proves that the
  index-two truncated second moment is slowly varying under the same
  hypothesis.
* `ProbabilityTheory.IsStableNorming.tendsto_nat_mul_truncatedSecondMoment_div_sq`:
  for an index-two stable norming $b_n$,
  $n\,V(b_n)/b_n^2\to1$, where $V(u)=\int_{|x|\le u}x^2\,\nu(dx)$.
* `ProbabilityTheory.IsStableNorming.tendsto_sq_div_nat`:
  if $\int x^2\,\nu(dx)<\infty$, then
  $b_n^2/n\to\int x^2\,\nu(dx)$.
* `ProbabilityTheory.IsStableNorming.tendsto_div_sqrt_nat`:
  if $\int x^2\,\nu(dx)<\infty$, then
  $b_n/\sqrt n\to\sqrt{\int x^2\,\nu(dx)}$.

This is the deterministic normalization step used to pass from the stable
index-two route to the finite-variance form of Donsker's theorem.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- For a probability law with positive second moment, the quadratic
stable norming relation holds for the canonical second-moment scale
`sqrt (n * secondMoment)`. -/
theorem isStableNorming_two_of_posSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsecondMoment : 0 < ∫ x, x ^ 2 ∂ν) :
    IsStableNorming 2 ν
      (fun n => Real.sqrt ((n : ℝ) * ∫ x, x ^ 2 ∂ν)) := by
  let secondMoment : ℝ := ∫ x, x ^ 2 ∂ν
  let normalization : ℕ → ℝ := fun n => Real.sqrt ((n : ℝ) * secondMoment)
  have hsquare : Integrable (fun x : ℝ => x ^ 2) ν :=
    Integrable.of_integral_ne_zero (ne_of_gt hsecondMoment)
  have hsecondMoment' : 0 < secondMoment := by simpa [secondMoment] using hsecondMoment
  have hnormalizationPos : ∀ n, 0 < n → 0 < normalization n := by
    intro n hn
    dsimp [normalization]
    exact Real.sqrt_pos.2 (mul_pos (by exact_mod_cast hn) hsecondMoment')
  have hnormalizationTop : Tendsto normalization atTop atTop := by
    have hnTop : Tendsto (fun n : ℕ => (n : ℝ) * secondMoment) atTop atTop := by
      simpa [mul_comm] using
        (tendsto_natCast_atTop_atTop.const_mul_atTop hsecondMoment')
    change Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) * secondMoment)) atTop atTop
    exact Real.tendsto_sqrt_atTop.comp hnTop
  have htruncated : Tendsto (fun u : ℝ => truncatedSecondMoment ν u) atTop
      (nhds secondMoment) := by
    simpa [secondMoment] using tendsto_truncatedSecondMoment ν hsquare
  have htruncatedNorm : Tendsto
      (fun n : ℕ => truncatedSecondMoment ν (normalization n)) atTop
      (nhds secondMoment) := htruncated.comp hnormalizationTop
  have htruncatedPos : ∀ᶠ n : ℕ in atTop,
      0 < truncatedSecondMoment ν (normalization n) :=
    htruncatedNorm.eventually (Ioi_mem_nhds hsecondMoment')
  have hnormRatio : Tendsto
      (fun n : ℕ => normalization n ^ (2 : ℝ) /
        stableSlowVariation 2 ν (normalization n) / (n : ℝ))
      atTop (nhds 1) := by
    have hlimit : Tendsto
        (fun n : ℕ => secondMoment / truncatedSecondMoment ν (normalization n))
        atTop (nhds 1) := by
      have hinv := htruncatedNorm.inv₀ hsecondMoment'.ne'
      have hmul : Tendsto
          (fun n : ℕ => secondMoment *
            (truncatedSecondMoment ν (normalization n))⁻¹)
          atTop (nhds (secondMoment * secondMoment⁻¹)) :=
        tendsto_const_nhds.mul hinv
      convert hmul using 1 <;> simp [div_eq_mul_inv, hsecondMoment'.ne']
    apply hlimit.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ), htruncatedPos]
      with n hn hmoment
    have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hscaleSq : normalization n ^ (2 : ℝ) = (n : ℝ) * secondMoment := by
      calc
        normalization n ^ (2 : ℝ) = normalization n ^ (2 : ℕ) :=
          Real.rpow_natCast (normalization n) 2
        _ = (Real.sqrt ((n : ℝ) * secondMoment)) ^ 2 := rfl
        _ = (n : ℝ) * secondMoment :=
          Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) hsecondMoment'.le)
    rw [stableSlowVariation_two, hscaleSq]
    dsimp [secondMoment]
    field_simp [hnReal, hmoment.ne']
  have hnorming : IsStableNorming 2 ν normalization :=
    ⟨hnormalizationPos, hnormalizationTop, hnormRatio⟩
  simpa [normalization, secondMoment] using hnorming

/-- A positive second moment makes the exponent-two factor `L*` slowly
varying: its truncated second moments converge to the full second moment. -/
theorem stableSlowVariation_two_isSlowlyVarying_of_posSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsecondMoment : 0 < ∫ x, x ^ 2 ∂ν) :
    Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation 2 ν) := by
  have hsquare : Integrable (fun x : ℝ => x ^ 2) ν :=
    Integrable.of_integral_ne_zero (ne_of_gt hsecondMoment)
  have hmoment := tendsto_truncatedSecondMoment ν hsquare
  have hslow : Asymptotics.IsSlowlyVaryingAtTop (truncatedSecondMoment ν) :=
    Asymptotics.IsSlowlyVaryingAtTop.of_tendsto_pos hsecondMoment hmoment
  rw [show stableSlowVariation 2 ν = truncatedSecondMoment ν by
    funext u
    exact stableSlowVariation_two ν u]
  exact hslow

/-- At exponent two, the stable norming relation yields the normalized
truncated-second-moment relation used for finite-variance comparisons. -/
theorem IsStableNorming.tendsto_nat_mul_truncatedSecondMoment_div_sq
    {ν : Measure ℝ} {normalization : ℕ → ℝ}
    (h : IsStableNorming 2 ν normalization) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      truncatedSecondMoment ν (normalization n) / normalization n ^ 2)
      atTop (nhds 1) := by
  let V : ℝ → ℝ := truncatedSecondMoment ν
  have hratio : Tendsto (fun n : ℕ => normalization n ^ (2 : ℝ) /
      V (normalization n) / (n : ℝ)) atTop (nhds 1) := by
    simpa only [stableSlowVariation_two] using h.2.2
  have hinv := hratio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hnatPos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact_mod_cast hn
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < normalization n :=
    h.2.1.eventually (eventually_gt_atTop 0)
  have hratioPos : ∀ᶠ n : ℕ in atTop,
      normalization n ^ (2 : ℝ) / V (normalization n) / (n : ℝ) > 0 :=
    hratio.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hVpos : ∀ᶠ n : ℕ in atTop, 0 < V (normalization n) := by
    filter_upwards [hscalePos, hnatPos, hratioPos] with n hb hn hq
    have hnum : 0 < normalization n ^ (2 : ℝ) / V (normalization n) :=
      (div_pos_iff_of_pos_right hn).mp hq
    have hpow : normalization n ^ (2 : ℝ) = normalization n ^ 2 :=
      Real.rpow_natCast (normalization n) 2
    rw [hpow] at hnum
    exact (div_pos_iff_of_pos_left (sq_pos_of_pos hb)).mp hnum
  have heq : (fun n : ℕ =>
      (normalization n ^ (2 : ℝ) / V (normalization n) / (n : ℝ))⁻¹) =ᶠ[atTop]
      fun n => (n : ℝ) * V (normalization n) / normalization n ^ 2 := by
    filter_upwards [hscalePos, hnatPos, hVpos] with n hb hn hV
    have hpow : normalization n ^ (2 : ℝ) = normalization n ^ 2 :=
      Real.rpow_natCast (normalization n) 2
    rw [hpow]
    field_simp [ne_of_gt hb, ne_of_gt hn, ne_of_gt hV]
  simpa [V] using hinv.congr' heq

/-- Under the asymptotic norming condition, the quadratic norming has the
variance scale in the limit when the increment law has a finite second moment. -/
theorem IsStableNorming.tendsto_sq_div_nat
    {ν : Measure ℝ} (hν : Integrable (fun x : ℝ => x ^ 2) ν)
    {b : ℕ → ℝ} (h : IsStableNorming 2 ν b) :
    Tendsto (fun n : ℕ => b n ^ 2 / (n : ℝ)) atTop
      (nhds (∫ x, x ^ 2 ∂ν)) := by
  have hnat : Tendsto (fun n : ℕ => truncatedSecondMoment ν (b n)) atTop
      (nhds (∫ x, x ^ 2 ∂ν)) :=
    (tendsto_truncatedSecondMoment ν hν).comp h.2.1
  have hratio : Tendsto
      (fun n : ℕ => stableScaleTime 2 ν (b n) / (n : ℝ)) atTop (nhds 1) := by
    simpa [stableScaleTime, stableSlowVariation_two] using h.2.2
  have hproduct : Tendsto
      (fun n : ℕ => stableScaleTime 2 ν (b n) / (n : ℝ) *
        truncatedSecondMoment ν (b n)) atTop
      (nhds (1 * (∫ x, x ^ 2 ∂ν))) := hratio.mul hnat
  have hratioPos : ∀ᶠ n : ℕ in atTop,
      0 < stableScaleTime 2 ν (b n) / (n : ℝ) := by
    simpa only [Set.mem_Ioi] using
      hratio.eventually (isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) < 1))
  have heq : (fun n : ℕ => b n ^ 2 / (n : ℝ)) =ᶠ[atTop]
      fun n => stableScaleTime 2 ν (b n) / (n : ℝ) *
        truncatedSecondMoment ν (b n) := by
    filter_upwards [hratioPos, eventually_gt_atTop 0] with n hr hn
    have hLne : truncatedSecondMoment ν (b n) ≠ 0 := by
      intro hzero
      have hpos := hr
      rw [stableScaleTime_two, hzero] at hpos
      simp at hpos
    rw [stableScaleTime_two]
    field_simp [hLne, show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne']
  simpa using hproduct.congr' heq.symm

/-- The same statement in the normalization used by Donsker's theorem. -/
theorem IsStableNorming.tendsto_div_sqrt_nat
    {ν : Measure ℝ} (hν : Integrable (fun x : ℝ => x ^ 2) ν)
    {b : ℕ → ℝ} (h : IsStableNorming 2 ν b) :
    Tendsto (fun n : ℕ => b n / Real.sqrt n) atTop
      (nhds (Real.sqrt (∫ x : ℝ, x ^ 2 ∂ν))) := by
  have hsq := h.tendsto_sq_div_nat hν
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (b n ^ 2 / (n : ℝ))) atTop
      (nhds (Real.sqrt (∫ x, x ^ 2 ∂ν))) :=
    (Real.continuous_sqrt.tendsto _).comp hsq
  refine hsqrt.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hbn : 0 < b n := h.1 n hn
  have hrewrite : b n ^ 2 / (n : ℝ) = (b n / Real.sqrt n) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hrewrite, Real.sqrt_sq
    (div_nonneg hbn.le (Real.sqrt_nonneg n))]

end ProbabilityTheory

end

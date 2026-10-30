/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Logarithmic trigonometric asymptotics

## Public declarations

* `Real.tendsto_log_sin_pi_div_add_log` states
  $\log\sin(\pi/L)+\log L\to\log\pi$ as $L\to\infty$.
* `Real.tendsto_log_cos_div_sq` states
  $\log(\cos x)/x^2\to-1/2$ as $x\to0$ through nonzero values.
* `Real.tendsto_sq_mul_log_cos_pi_div` states
  $L^2\log\cos(\pi/L)\to-\pi^2/2$ as $L\to\infty$.
* `Real.tendsto_cos_pi_div_rpow_zero` states that if $L_n\to\infty$,
  $t_n>0$, and $L_n^2/t_n\to0$, then
  $\cos^{t_n}(\pi/L_n)\to0$. -/

open Filter
open scoped Topology

@[expose] public section

namespace Real

/-- The logarithmic sine prefactor has the asymptotic size `π / length`. -/
theorem tendsto_log_sin_pi_div_add_log :
    Tendsto (fun length : ℝ =>
      Real.log (Real.sin (Real.pi / length)) + Real.log length)
      atTop (𝓝 (Real.log Real.pi)) := by
  have hzero : Tendsto (fun length : ℝ => Real.pi / length)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hpunc : Tendsto (fun length : ℝ => Real.pi / length)
      atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hzero, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with length hlength
    simp [Real.pi_ne_zero, hlength.ne']
  have hratio : Tendsto (fun length : ℝ =>
      Real.sin (Real.pi / length) / (Real.pi / length))
      atTop (𝓝 1) := by
    convert Real.tendsto_sin_div_nhdsNE_zero.comp hpunc using 1
    funext length
    rfl
  have hlogRatio : Tendsto (fun length : ℝ =>
      Real.log (Real.sin (Real.pi / length) / (Real.pi / length)))
      atTop (𝓝 0) := by
    have hlog : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
      simpa using (Real.continuousAt_log one_ne_zero).tendsto
    exact hlog.comp hratio
  have htarget := hlogRatio.add_const (Real.log Real.pi)
  have heq : (fun length : ℝ =>
      Real.log (Real.sin (Real.pi / length) / (Real.pi / length)) +
        Real.log Real.pi) =ᶠ[atTop]
      (fun length : ℝ =>
        Real.log (Real.sin (Real.pi / length)) + Real.log length) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with length hlength
    have hlengthPos : 0 < length := zero_lt_one.trans hlength
    have hzPos : 0 < Real.pi / length := div_pos Real.pi_pos hlengthPos
    have hzLtPi : Real.pi / length < Real.pi := by
      exact (div_lt_iff₀ hlengthPos).2 (by nlinarith [Real.pi_pos])
    have hsinPos : 0 < Real.sin (Real.pi / length) :=
      Real.sin_pos_of_pos_of_lt_pi hzPos hzLtPi
    rw [← Real.log_mul hsinPos.ne' hlengthPos.ne',
      ← Real.log_mul (div_pos hsinPos hzPos).ne' Real.pi_ne_zero]
    congr 1
    field_simp [Real.pi_ne_zero, hlengthPos.ne']
  simpa only [zero_add] using htarget.congr' heq

/-- The local logarithmic asymptotic of cosine. -/
theorem tendsto_log_cos_div_sq :
    Tendsto (fun x : ℝ => Real.log (Real.cos x) / x ^ 2)
      (𝓝[≠] 0) (𝓝 (-1 / 2 : ℝ)) := by
  apply HasDerivAt.lhopital_zero_nhdsNE
      (f' := fun x => -Real.tan x) (g' := fun x => 2 * x)
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (Real.continuous_cos.continuousAt.eventually_ne (by norm_num : Real.cos 0 ≠ 0))] with x hx
    convert (Real.hasDerivAt_cos x).log hx using 1
    rw [Real.tan_eq_sin_div_cos, neg_div]
  · exact Eventually.of_forall fun x => by simpa using (hasDerivAt_pow 2 x)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  · have hc : Tendsto Real.cos (𝓝 (0 : ℝ)) (𝓝 1) := by
      simpa using Real.continuous_cos.tendsto 0
    have hl : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
      simpa using (Real.continuousAt_log one_ne_zero).tendsto
    exact tendsto_nhdsWithin_of_tendsto_nhds (hl.comp hc)
  · exact tendsto_nhdsWithin_of_tendsto_nhds <| by
      simpa using (continuous_pow 2).tendsto (0 : ℝ)
  · have h := Real.tendsto_tan_div_nhdsNE_zero.const_mul (-1 / 2 : ℝ)
    convert h using 1
    · funext x
      field_simp
    · norm_num

/-- The diffusive logarithmic limit of the cosine:
$L^2\log\cos(\pi/L)\to-\pi^2/2$ as $L\to\infty$. -/
theorem tendsto_sq_mul_log_cos_pi_div :
    Tendsto (fun length : ℝ =>
      length ^ 2 * Real.log (Real.cos (Real.pi / length)))
      atTop (𝓝 (-(Real.pi ^ 2) / 2)) := by
  have hzero : Tendsto (fun length : ℝ => Real.pi / length) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hpunc : Tendsto (fun length : ℝ => Real.pi / length)
      atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hzero, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with length hlength
    simp [Real.pi_ne_zero, hlength.ne']
  have h := (tendsto_log_cos_div_sq.comp hpunc).const_mul (Real.pi ^ 2)
  have hbase : Tendsto (fun length : ℝ => Real.pi ^ 2 *
      (Real.log (Real.cos (Real.pi / length)) / (Real.pi / length) ^ 2))
      atTop (𝓝 (Real.pi ^ 2 * (-1 / 2 : ℝ))) := by
    simpa only [Function.comp_apply] using h
  have h' : Tendsto (fun length : ℝ => Real.pi ^ 2 *
      (Real.log (Real.cos (Real.pi / length)) / (Real.pi / length) ^ 2))
      atTop (𝓝 (-(Real.pi ^ 2) / 2)) := by
    have heq : Real.pi ^ 2 * (-1 / 2 : ℝ) = -(Real.pi ^ 2) / 2 := by ring
    rw [← heq]
    exact hbase
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with length hlength
  field_simp [Real.pi_ne_zero, hlength.ne']

/-- If the width grows, positive real times dominate its square, and the
cosine remains positive, then the corresponding real power tends to zero.
This analytic statement is independent of a particular finite-state process. -/
theorem tendsto_cos_pi_div_rpow_zero
    (width time : ℕ → ℝ)
    (hwidthTwo : ∀ n, 2 < width n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto width atTop atTop)
    (hratio : Tendsto (fun n => width n ^ 2 / time n)
      atTop (nhds 0)) :
    Tendsto (fun n => Real.cos (Real.pi / width n) ^ time n)
      atTop (nhds 0) := by
  let ratio : ℕ → ℝ := fun n => width n ^ 2 / (time n : ℝ)
  let eigenvalue : ℕ → ℝ := fun n => Real.cos (Real.pi / width n)
  let main : ℕ → ℝ := fun n => width n ^ 2 * Real.log (eigenvalue n)
  have hmain : Tendsto main atTop (nhds (-(Real.pi ^ 2) / 2)) := by
    convert tendsto_sq_mul_log_cos_pi_div.comp hwidth using 1
    funext n
    simp [main, eigenvalue, Function.comp_apply]
  have hratioPos : ∀ n, 0 < ratio n := by
    intro n
    dsimp [ratio]
    apply div_pos
    · exact sq_pos_of_pos (by linarith [hwidthTwo n])
    · exact htime n
  have hratioGT : Tendsto ratio atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hratio, Eventually.of_forall hratioPos⟩
  have hinv : Tendsto ratio⁻¹ atTop atTop :=
    hratioGT.inv_tendsto_nhdsGT_zero
  have hconstantNeg : -(Real.pi ^ 2) / 2 < 0 := by
    nlinarith [sq_pos_of_pos Real.pi_pos]
  have hexponent : Tendsto (fun n => main n * (ratio n)⁻¹)
      atTop atBot := hmain.neg_mul_atTop hconstantNeg hinv
  have hexp : Tendsto (fun n => Real.exp (main n * (ratio n)⁻¹))
      atTop (nhds 0) := Real.tendsto_exp_atBot.comp hexponent
  apply hexp.congr'
  filter_upwards with n
  have hwidthPos : 0 < width n := by linarith [hwidthTwo n]
  have hanglePos : 0 < Real.pi / width n := div_pos Real.pi_pos hwidthPos
  have hangleLt : Real.pi / width n < Real.pi / 2 := by
    rw [div_lt_div_iff₀ hwidthPos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.pi_pos, hwidthTwo n]
  have heigenvalue : 0 < eigenvalue n :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hanglePos, Real.pi_pos], hangleLt⟩
  have htimeReal : time n ≠ 0 := ne_of_gt (htime n)
  have hwidthReal : width n ≠ 0 := ne_of_gt hwidthPos
  have hexponentEq : main n * (ratio n)⁻¹ =
      time n * Real.log (eigenvalue n) := by
    dsimp [main, ratio]
    rw [inv_div]
    field_simp [hwidthReal, htimeReal]
  rw [hexponentEq, Real.rpow_def_of_pos heigenvalue]
  congr 1
  ring

end Real

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The exceptional-event expectation in the speed bound

## Internal proof declarations

* `tendsto_setIntegral_div_log_of_failure`: if
  $\|Y_N\|_2\le C(\log N)^3$ and $P(E_N^c)\le N^{-b}$ with $b>0$, then
  $\mathbb E[Y_N\mathbf1_{E_N^c}]/\log N\to 0$.

This is the Cauchy–Schwarz step in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Theorem 1.2.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

private lemma abs_setIntegral_le_sqrt_mul
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : MemLp Y 2 P) (A : Set Ω) :
    |∫ ω in A, Y ω ∂P| ≤
      Real.sqrt (∫ ω, (Y ω) ^ 2 ∂P) * Real.sqrt (P.real A) := by
  have hconst : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal 2) (P.restrict A) :=
    memLp_const _
  have hYr : MemLp Y (ENNReal.ofReal 2) (P.restrict A) := by
    norm_num
    exact hY.restrict A
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hh := integral_mul_norm_le_Lp_mul_Lq hpq hYr hconst
  simp only [norm_one, mul_one, integral_const, smul_eq_mul, mul_one,
    Measure.restrict_apply_univ, measureReal_def, Real.norm_eq_abs, Real.rpow_two, sq_abs,
    ← Real.sqrt_eq_rpow] at hh
  have hsq : (∫ ω in A, Y ω ^ 2 ∂P) ≤ ∫ ω, Y ω ^ 2 ∂P := by
    exact integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun _ => sq_nonneg _)
      hY.integrable_sq
  calc
    _ ≤ ∫ ω in A, |Y ω| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := P.restrict A) Y
    _ ≤ Real.sqrt (∫ ω in A, Y ω ^ 2 ∂P) * Real.sqrt (P.real A) := by
      simpa [Real.sqrt_eq_rpow, measureReal_def] using hh
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsq) (Real.sqrt_nonneg _)

lemma tendsto_setIntegral_div_log_of_failure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (A : ℕ → Set Ω) (hY : ∀ᶠ n in atTop, MemLp (Y n) 2 P)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {C b : ℝ} (hC : 0 ≤ C) (hb : 0 < b)
    (hsecond : ∀ᶠ n in atTop,
      Real.sqrt (∫ ω, (Y n ω) ^ 2 ∂P) ≤ C * Real.log (N n : ℝ) ^ 3)
    (hprob : ∀ᶠ n in atTop, P.real (A n) ≤ Real.exp (-b * Real.log (N n : ℝ))) :
    Tendsto (fun n => (∫ ω in A n, Y n ω ∂P) / Real.log (N n : ℝ)) atTop (𝓝 0) := by
  let L := fun n => Real.log (N n : ℝ)
  have hL : Tendsto L atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hdecay : Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-(b / 2) * x)) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
    have hc : Tendsto (fun x : ℝ => (b / 2) * x) atTop atTop :=
      tendsto_id.const_mul_atTop (by positivity)
    have h' : Tendsto (fun x : ℝ =>
        (b / 2)⁻¹ ^ 2 * (((b / 2) * x) ^ 2 * Real.exp (-((b / 2) * x)))) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_apply] using (h.comp hc).const_mul ((b / 2)⁻¹ ^ 2)
    refine h'.congr fun x => ?_
    have hb' : b / 2 ≠ 0 := (by positivity : 0 < b / 2).ne'
    field_simp [hb']
  have hlim : Tendsto (fun n => C * (L n ^ 2 * Real.exp (-(b / 2) * L n))) atTop (𝓝 0) := by
    simpa using (hdecay.comp hL).const_mul C
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hY, hsecond, hprob, hL.eventually_gt_atTop 0] with n hYn h₂ hp hlog
  have hroot : Real.sqrt (P.real (A n)) ≤ Real.exp (-(b / 2) * L n) := by
    refine (Real.sqrt_le_sqrt hp).trans_eq ?_
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hlog]
  apply (div_le_iff₀ hlog).2
  have hholder := abs_setIntegral_le_sqrt_mul P (Y n) hYn (A n)
  calc
    _ ≤ (C * L n ^ 3) * Real.exp (-(b / 2) * L n) :=
      hholder.trans (mul_le_mul h₂ hroot (Real.sqrt_nonneg _) (by positivity))
    _ = _ := by ring

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# First moments on exponentially rare events

## Public declarations

* `MeasureTheory.tendsto_setIntegral_div_of_polynomial_second_moment_and_exponential_probability`:
  for any diverging real scale `L_i`, real exponent `r`, and `C≥0,b>0`,
  `‖Y_i‖₂≤C L_i^r` and `P(A_i)≤exp(-b L_i)` imply
  `E[Y_i 1_(A_i)]/L_i→0`. The variables are eventually in `L²`;
  the filter and measurable finite measure space are arbitrary.

Native Hölder and real-power/exponential asymptotics supply the proof.
This generalizes the exceptional-event estimate used by Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 4, Theorem 1.2, beyond logarithmic scales
and its cubic moment envelope.
-/

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace MeasureTheory

private lemma abs_setIntegral_le_sqrt_mul
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
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

/-- A polynomial `L²` envelope is negligible on events exponentially small
in a diverging scale, after normalization by that scale. This is Hölder's
inequality and native real-power/exponential decay. -/
theorem tendsto_setIntegral_div_of_polynomial_second_moment_and_exponential_probability
    {ι Ω : Type*} [MeasurableSpace Ω] {l : Filter ι}
    (P : Measure Ω) [IsFiniteMeasure P]
    (Y : ι → Ω → ℝ) (A : ι → Set Ω)
    {L : ι → ℝ} (hL : Tendsto L l atTop)
    (hY : ∀ᶠ i in l, MemLp (Y i) 2 P)
    {C b r : ℝ} (hC : 0 ≤ C) (hb : 0 < b)
    (hsecond : ∀ᶠ i in l, Real.sqrt (∫ ω, (Y i ω) ^ 2 ∂P) ≤ C * L i ^ r)
    (hprob : ∀ᶠ i in l, P.real (A i) ≤ Real.exp (-b * L i)) :
    Tendsto (fun i => (∫ ω in A i, Y i ω ∂P) / L i) l (𝓝 0) := by
  have hlim : Tendsto (fun i => C * (L i ^ (r - 1) * Real.exp (-(b / 2) * L i)))
      l (𝓝 0) := by
    simpa using ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (r - 1) (b / 2) (half_pos hb)).comp hL).const_mul C
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hY, hsecond, hprob, hL.eventually_gt_atTop 0] with i hYi h₂ hp hLi
  have hroot : Real.sqrt (P.real (A i)) ≤ Real.exp (-(b / 2) * L i) := by
    refine (Real.sqrt_le_sqrt hp).trans_eq ?_
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hLi]
  apply (div_le_iff₀ hLi).2
  have hpow : L i ^ r = L i ^ (r - 1) * L i := by
    calc
      _ = L i ^ ((r - 1) + 1) := by congr 1; ring
      _ = L i ^ (r - 1) * L i ^ (1 : ℝ) := Real.rpow_add hLi _ _
      _ = _ := by rw [Real.rpow_one]
  calc
    _ ≤ (C * L i ^ r) * Real.exp (-(b / 2) * L i) :=
      (abs_setIntegral_le_sqrt_mul P (Y i) hYi (A i)).trans
        (mul_le_mul h₂ hroot (Real.sqrt_nonneg _) (by positivity))
    _ = _ := by rw [hpow]; ring

end MeasureTheory

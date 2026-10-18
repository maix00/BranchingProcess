/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
* `ProbabilityTheory.measure_ge_threshold_of_moments`: for a nonnegative
  square-integrable random variable `X` on a probability space, with mean `m`,
  second moment `s > 0`, and `0 ≤ t < m`,
  `(m - t) ^ 2 / s ≤ ℙ(t ≤ X)`.
* `ProbabilityTheory.measure_ge_threshold_of_secondMoment_le`: if in addition
  `2 * t ≤ m` and `s ≤ C * m ^ 2` for `C > 0`, then
  `1 / (4 * C) ≤ ℙ(t ≤ X)`.

# Paley--Zygmund inequalities

These statements depend only on the first two moments of a nonnegative random
variable on a probability space. They do not depend on a particular process
or distribution. The first inequality is the random-variable form of Paley and
Zygmund, [*On some series of functions, (3)*, Lemma 19, p. 192
(1932)](https://doi.org/10.1017/S0305004100010860).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

/-- A second-moment lower bound for a threshold event on a probability space.
This is the Paley--Zygmund estimate. -/
theorem measure_ge_threshold_of_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXmeas : Measurable X)
    (hX_nonneg : 0 ≤ᵐ[μ] X)
    (hX_integrable : Integrable X μ)
    (hX_memLp : MemLp X 2 μ)
    (mean second threshold : ℝ)
    (hmean : ∫ ω, X ω ∂μ = mean)
    (hsecond : ∫ ω, X ω ^ 2 ∂μ = second)
    (hthreshold : 0 ≤ threshold) (hmean_threshold : threshold < mean)
    (hsecond_pos : 0 < second) :
    (μ.real {ω | threshold ≤ X ω}) ≥ (mean - threshold) ^ 2 / second := by
  let A : Set Ω := {ω | threshold ≤ X ω}
  have hA : MeasurableSet A := hXmeas measurableSet_Ici
  have hX2_integrable : Integrable (fun ω => X ω ^ 2) μ := hX_memLp.integrable_sq
  have hX2_nonneg : 0 ≤ᵐ[μ] fun ω => X ω ^ 2 := by
    filter_upwards [hX_nonneg] with ω hω
    exact sq_nonneg (X ω)
  have hmeasureAc : μ.real Aᶜ ≤ 1 := by
    calc
      μ.real Aᶜ ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp
  have hcompl_bound : (∫ ω in Aᶜ, X ω ∂μ) ≤ threshold := by
    calc
      (∫ ω in Aᶜ, X ω ∂μ) ≤ ∫ ω in Aᶜ, (fun _ => threshold) ω ∂μ := by
        apply setIntegral_mono_on hX_integrable.integrableOn
          (integrable_const threshold).integrableOn hA.compl
        intro ω hω
        simp only [Set.mem_compl_iff] at hω
        exact (not_le.mp hω).le
      _ = μ.real Aᶜ * threshold := by
        rw [integral_const, smul_eq_mul]
        rw [measureReal_restrict_apply_univ]
      _ ≤ threshold := by nlinarith [mul_nonneg hthreshold (sub_nonneg.mpr hmeasureAc)]
  have hA_lower : mean - threshold ≤ ∫ ω in A, X ω ∂μ := by
    have hsplit := integral_add_compl hA hX_integrable
    rw [hmean] at hsplit
    linarith
  let μA : Measure Ω := μ.restrict A
  have hX_nonnegA : 0 ≤ᵐ[μA] X := by
    exact ae_mono Measure.restrict_le_self hX_nonneg
  have hX_memLpA : MemLp X 2 μA := by
    exact hX_memLp.mono_measure Measure.restrict_le_self
  have hOne_memLpA : MemLp (fun _ : Ω => (1 : ℝ)) 2 μA := memLp_const _
  have hOne_nonnegA : 0 ≤ᵐ[μA] fun _ : Ω => (1 : ℝ) := ae_of_all _ (fun _ => by norm_num)
  have h22 : (2 : ℝ).HolderConjugate 2 := by
    convert Real.HolderConjugate.conjExponent (show 1 < (2 : ℝ) by norm_num) using 1
    norm_num [Real.conjExponent]
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg h22 hX_nonnegA hOne_nonnegA
    (by simpa using hX_memLpA) (by simpa using hOne_memLpA)
  have hsq_restrict_le :
      ∫ ω, X ω ^ 2 ∂μA ≤ second := by
    calc
      ∫ ω, X ω ^ 2 ∂μA ≤ ∫ ω, X ω ^ 2 ∂μ := by
        exact integral_mono_measure Measure.restrict_le_self hX2_nonneg hX2_integrable
      _ = second := hsecond
  have hmeasureA_nonneg : 0 ≤ μ.real A := measureReal_nonneg
  have hHolder_set :
      (∫ ω in A, X ω ∂μ) ≤ Real.sqrt second * Real.sqrt (μ.real A) := by
    have hHolder' :
        (∫ ω in A, X ω ∂μ) ≤
          Real.sqrt (∫ ω, X ω ^ 2 ∂μA) * Real.sqrt ((μA).real Set.univ) := by
      simpa [μA, integral_const, smul_eq_mul, Real.sqrt_eq_rpow] using hHolder
    have hsqrtmean :
        Real.sqrt (∫ ω, X ω ^ 2 ∂μA) ≤ Real.sqrt second :=
      Real.sqrt_le_sqrt hsq_restrict_le
    have hsqrtprob : Real.sqrt ((μA).real Set.univ) = Real.sqrt (μ.real A) := by
      simp [μA]
    rw [hsqrtprob] at hHolder'
    exact hHolder'.trans (mul_le_mul_of_nonneg_right hsqrtmean (Real.sqrt_nonneg _))
  have hleft_nonneg : 0 ≤ mean - threshold := by linarith
  have hright_nonneg : 0 ≤ Real.sqrt second * Real.sqrt (μ.real A) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq_bound : (mean - threshold) ^ 2 ≤ second * μ.real A := by
    have hlin : mean - threshold ≤ Real.sqrt second * Real.sqrt (μ.real A) :=
      hA_lower.trans hHolder_set
    have hsq := (sq_le_sq₀ hleft_nonneg hright_nonneg).2 hlin
    simpa only [mul_pow, Real.sq_sqrt hsecond_pos.le,
      Real.sq_sqrt hmeasureA_nonneg] using hsq
  have hdiv : (mean - threshold) ^ 2 / second ≤ μ.real A :=
    (div_le_iff₀ hsecond_pos).2 (by nlinarith [hsq_bound])
  exact hdiv

/-- If the mean is at least twice the threshold and the second moment is at
most `C` times the squared mean, the threshold is reached with probability at
least `1 / (4 * C)`. -/
theorem measure_ge_threshold_of_secondMoment_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXmeas : Measurable X)
    (hX_nonneg : 0 ≤ᵐ[μ] X)
    (hX_integrable : Integrable X μ)
    (hX_memLp : MemLp X 2 μ)
    (mean second threshold C : ℝ)
    (hmean : ∫ ω, X ω ∂μ = mean)
    (hsecond : ∫ ω, X ω ^ 2 ∂μ = second)
    (hthreshold : 0 ≤ threshold) (hmean_pos : 0 < mean)
    (hthreshold_le : 2 * threshold ≤ mean)
    (hsecond_pos : 0 < second)
    (hC_pos : 0 < C) (hsecond_le : second ≤ C * mean ^ 2) :
    (μ.real {ω | threshold ≤ X ω}) ≥ 1 / (4 * C) := by
  have hmean_threshold : threshold < mean := by linarith
  have hPZ := measure_ge_threshold_of_moments μ X hXmeas hX_nonneg
    hX_integrable hX_memLp mean second threshold hmean hsecond hthreshold
    hmean_threshold hsecond_pos
  have hgap : mean / 2 ≤ mean - threshold := by linarith
  have hgap_nonneg : 0 ≤ mean - threshold := by linarith
  have hgap_sq : mean ^ 2 / 4 ≤ (mean - threshold) ^ 2 := by
    nlinarith [sq_nonneg (mean / 2), sq_nonneg (mean - threshold)]
  have hfrac : 1 / (4 * C) ≤ (mean - threshold) ^ 2 / second := by
    apply (le_div_iff₀ hsecond_pos).2
    have hnum : second / (4 * C) ≤ mean ^ 2 / 4 := by
      have hmul := div_le_div_of_nonneg_right hsecond_le (by positivity : 0 ≤ 4 * C)
      convert hmul using 1
      field_simp
    have hleft : 1 / (4 * C) * second = second / (4 * C) := by
      field_simp [hC_pos.ne']
    rw [hleft]
    exact hnum.trans hgap_sq
  exact le_trans hfrac hPZ

end ProbabilityTheory

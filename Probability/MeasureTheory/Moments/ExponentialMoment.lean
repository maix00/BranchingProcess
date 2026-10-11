/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/-!
# Moment bounds from exponential moments

These estimates apply to measurable real-valued random variables on arbitrary
probability spaces. They do not depend on a particular distribution.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

/-- A finite exponential moment of `-X` controls the fourth moment of its
negative part. The hypothesis is stated using the nonnegative integral so
finiteness also yields the integrability needed for the Bochner moment.

For `B ≥ 1`, the explicit universal constant `2048` gives
`E[(max (-X) 0)^4] ≤ 2048 * (1 + log(B)^4)`. -/
theorem integrable_pow_four_max_neg_of_lintegral_exp_neg_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    {B : ℝ} (hB : 1 ≤ B)
    (hExp : (∫⁻ ω, ENNReal.ofReal (Real.exp (-X ω)) ∂μ) ≤ ENNReal.ofReal B) :
    Integrable (fun ω => (max (-X ω) 0) ^ 4) μ ∧
      (∫ ω, (max (-X ω) 0) ^ 4 ∂μ) ≤
        2048 * (1 + Real.log B ^ 4) := by
  let L : ℝ := Real.log B
  let y : Ω → ℝ := fun ω => max (-X ω) 0
  let A : Set Ω := {ω | L < y ω}
  let oneA : Ω → ℝ := A.indicator (fun _ => (1 : ℝ))
  let expA : Ω → ℝ := A.indicator (fun ω => Real.exp (-X ω))
  let f : Ω → ℝ := fun ω => y ω ^ 4
  let g : Ω → ℝ := fun ω => L ^ 4 + (8 * L ^ 4) * oneA ω +
    (2048 * Real.exp (-L)) * expA ω

  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg hB
  have hL4 : 0 ≤ L ^ 4 := by positivity
  have hBpos : 0 < B := by linarith
  have hA : MeasurableSet A := by
    exact measurableSet_lt measurable_const (by
      dsimp [y]
      fun_prop)

  have hExpMeas : Measurable (fun ω => Real.exp (-X ω)) := by fun_prop
  have hExpLNeTop :
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-X ω)) ∂μ) ≠ ∞ := by
    apply ne_of_lt (lt_of_le_of_lt hExp ?_)
    simp
  have hExpInt : Integrable (fun ω => Real.exp (-X ω)) μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hExpMeas.aestronglyMeasurable
      (ae_of_all μ fun ω => Real.exp_nonneg _)).mp hExpLNeTop
  have hExpBound : (∫ ω, Real.exp (-X ω) ∂μ) ≤ B := by
    have hExpEq := ofReal_integral_eq_lintegral_ofReal hExpInt
      (ae_of_all μ fun ω => Real.exp_nonneg _)
    rw [← hExpEq] at hExp
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hExp

  have hOneAInt : Integrable oneA μ := by
    dsimp [oneA]
    exact (integrable_const (1 : ℝ)).indicator hA
  have hExpAInt : Integrable expA μ := by
    dsimp [expA]
    exact hExpInt.indicator hA
  have hGInt : Integrable g μ := by
    dsimp [g]
    exact ((integrable_const _).add (hOneAInt.const_mul (8 * L ^ 4))).add
      (hExpAInt.const_mul (2048 * Real.exp (-L)))

  have hOneAIntegral : (∫ ω, oneA ω ∂μ) = μ.real A := by
    simpa [oneA] using integral_indicator_const (1 : ℝ) hA
  have hExpAIntegralLe : (∫ ω, expA ω ∂μ) ≤
      ∫ ω, Real.exp (-X ω) ∂μ := by
    apply integral_mono_ae hExpAInt hExpInt
    filter_upwards [] with ω
    by_cases hω : ω ∈ A
    · simp [expA, hω]
    · simp [expA, hω]
      exact Real.exp_nonneg _
  have hAprob : μ.real A ≤ 1 := by
    calc
      μ.real A ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := probReal_univ
  have hExpScale : Real.exp (-L) * B = 1 := by
    dsimp [L]
    rw [Real.exp_neg, Real.exp_log hBpos]
    field_simp

  have hGIntegral :
      (∫ ω, g ω ∂μ) = L ^ 4 + (8 * L ^ 4) * μ.real A +
        (2048 * Real.exp (-L)) * (∫ ω, expA ω ∂μ) := by
    calc
      (∫ ω, g ω ∂μ) =
          (∫ ω, L ^ 4 + (8 * L ^ 4) * oneA ω ∂μ) +
            (∫ ω, (2048 * Real.exp (-L)) * expA ω ∂μ) := by
              rw [show g = fun ω =>
                (L ^ 4 + (8 * L ^ 4) * oneA ω) +
                  (2048 * Real.exp (-L)) * expA ω by
                    funext ω
                    simp [g]
                    ]
              exact integral_add ((integrable_const _).add
                (hOneAInt.const_mul (8 * L ^ 4)))
                (hExpAInt.const_mul (2048 * Real.exp (-L)))
      _ = (∫ ω, (L ^ 4 : ℝ) ∂μ) +
            (∫ ω, (8 * L ^ 4) * oneA ω ∂μ) +
            (∫ ω, (2048 * Real.exp (-L)) * expA ω ∂μ) := by
              rw [integral_add (integrable_const _)
                (hOneAInt.const_mul (8 * L ^ 4))]
      _ = L ^ 4 + (8 * L ^ 4) * μ.real A +
            (2048 * Real.exp (-L)) * (∫ ω, expA ω ∂μ) := by
              rw [integral_const, probReal_univ, one_smul,
                integral_const_mul, hOneAIntegral, integral_const_mul]

  have hGIntegralBound :
      (∫ ω, g ω ∂μ) ≤ 2048 * (1 + L ^ 4) := by
    rw [hGIntegral]
    have hExpAToB : (∫ ω, expA ω ∂μ) ≤ B := hExpAIntegralLe.trans hExpBound
    have hScaleBound :
        (2048 * Real.exp (-L)) * (∫ ω, expA ω ∂μ) ≤ 2048 := by
      calc
        (2048 * Real.exp (-L)) * (∫ ω, expA ω ∂μ) ≤
            (2048 * Real.exp (-L)) * B :=
              mul_le_mul_of_nonneg_left hExpAToB (by positivity)
        _ = 2048 := by rw [mul_assoc, hExpScale]; norm_num
    nlinarith [hAprob, hL4, hScaleBound]

  have hPoint : ∀ ω, f ω ≤ g ω := by
    intro ω
    by_cases hω : ω ∈ A
    · have hyL : L < y ω := by simpa [A] using hω
      have hXneg : X ω < 0 := by
        by_contra hnot
        have hXnonneg : 0 ≤ X ω := le_of_not_gt hnot
        have hyzero : y ω = 0 := by
          simp [y, max_eq_right (neg_nonpos.mpr hXnonneg)]
        linarith [hyL]
      have hyEq : y ω = -X ω := by
        simp [y, max_eq_left (neg_nonneg.mpr hXneg.le)]
      let s : ℝ := y ω - L
      have hs : 0 ≤ s := by dsimp [s]; linarith
      have hsExp : s ≤ 4 * Real.exp (s / 4) := by
        have h := Real.add_one_le_exp (s / 4)
        have hs4 : 0 ≤ s / 4 := by positivity
        nlinarith
      have hsPow : s ^ 4 ≤ 256 * Real.exp s := by
        have hpow : s ^ 4 ≤ (4 * Real.exp (s / 4)) ^ 4 := by
          gcongr
        calc
          s ^ 4 ≤ (4 * Real.exp (s / 4)) ^ 4 := hpow
          _ = 256 * Real.exp s := by
            rw [mul_pow, ← Real.exp_nat_mul]
            norm_num
            ring
      have hsumPow : (L + s) ^ 4 ≤ 8 * (L ^ 4 + s ^ 4) := by
        have h := add_pow_le hL hs 4
        norm_num at h
        exact h
      have hySum : y ω = L + s := by dsimp [s]; ring
      have hpoly : y ω ^ 4 ≤ 8 * L ^ 4 + 2048 * Real.exp s := by
        rw [hySum]
        calc
          (L + s) ^ 4 ≤ 8 * (L ^ 4 + s ^ 4) := hsumPow
          _ ≤ 8 * L ^ 4 + 2048 * Real.exp s := by nlinarith [hsPow]
      have hsEq : s = -L + -X ω := by
        dsimp [s]
        rw [hyEq]
        ring
      have hExpEq : Real.exp s = Real.exp (-L) * Real.exp (-X ω) := by
        rw [hsEq, Real.exp_add]
      have hpoly' : y ω ^ 4 ≤ 8 * L ^ 4 +
          2048 * (Real.exp (-L) * Real.exp (-X ω)) := by
        calc
          y ω ^ 4 ≤ 8 * L ^ 4 + 2048 * Real.exp s := hpoly
          _ = 8 * L ^ 4 + 2048 *
              (Real.exp (-L) * Real.exp (-X ω)) := by rw [hExpEq]
      have hmajor : y ω ^ 4 ≤ L ^ 4 + (8 * L ^ 4) +
          (2048 * Real.exp (-L)) * Real.exp (-X ω) := by
        nlinarith [hL4, hpoly']
      simpa [f, g, oneA, expA, hω] using hmajor
    · have hyLe : y ω ≤ L := le_of_not_gt (by
        simpa [A] using hω)
      have hlow : y ω ^ 4 ≤ L ^ 4 := by
        exact pow_le_pow_left₀ (by positivity) hyLe 4
      have hOne : oneA ω = 0 := by simp [oneA, hω]
      have hExpA : expA ω = 0 := by simp [expA, hω]
      simpa [f, g, hOne, hExpA] using hlow

  have hYMeas : Measurable y := by
    dsimp [y]
    fun_prop
  have hFMeas : Measurable f := by
    dsimp [f]
    fun_prop
  have hFNonneg (ω : Ω) : 0 ≤ f ω := by positivity
  have hOneANonneg (ω : Ω) : 0 ≤ oneA ω := by
    by_cases hω : ω ∈ A <;> simp [oneA, hω]
  have hExpANonneg (ω : Ω) : 0 ≤ expA ω := by
    by_cases hω : ω ∈ A
    · simp [expA, hω]
      exact Real.exp_nonneg _
    · simp [expA, hω]
  have hGNonneg (ω : Ω) : 0 ≤ g ω := by
    dsimp [g]
    exact add_nonneg
      (add_nonneg hL4 (mul_nonneg (by positivity) (hOneANonneg ω)))
      (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_nonneg _))
        (hExpANonneg ω))
  have hFInt : Integrable f μ := by
    apply hGInt.mono' hFMeas.aestronglyMeasurable
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hFNonneg ω),
      abs_of_nonneg (hGNonneg ω)] using hPoint ω
  have hIntegralBound : (∫ ω, f ω ∂μ) ≤ 2048 * (1 + L ^ 4) := by
    have hmono := integral_mono_ae hFInt hGInt (ae_of_all μ hPoint)
    exact hmono.trans hGIntegralBound

  exact ⟨by simpa [f, y] using hFInt,
    by simpa [f, y, L] using hIntegralBound⟩

end ProbabilityTheory

end

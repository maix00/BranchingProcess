/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Range.Rate
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Explicit finite-cover parameter limits

The finite-cover block estimate has a fixed multiplicative prefactor and a
spectral exponent. This file isolates the elementary real-analysis step that
chooses cover count, Donsker slack, and diffusive block constant in the order
required by the proof.
-/

open Filter

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- At diffusive width `(1 + enlargement) / √C`, the finite-cover spectral
exponential has an exponent linear in `C`. -/
theorem finiteCoverCorridorExponential_diffusive
    {count : ℕ} (hcount : 0 < count)
    {enlargement C : ℝ} (henlargement : 0 < enlargement) (hC : 0 < C) :
    finiteCoverCorridorExponential count ((1 + enlargement) / Real.sqrt C) =
      Real.exp (-(Real.pi ^ 2 / (2 *
        (((1 + 3 / (count : ℝ)) * (1 + enlargement)) ^ 2)) * C)) := by
  have hcountCast : (count : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcount.ne'
  have hsqrt : Real.sqrt C ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hC)
  unfold finiteCoverCorridorExponential
  congr 1
  field_simp [hsqrt, hcountCast]
  rw [Real.sq_sqrt hC.le]

/-- The logarithmic fixed-cover bound is an affine function of the reciprocal
block constant, with its limiting spectral coefficient explicit. -/
theorem scaledLog_two_finiteCoverRangeBound_diffusive
    {count : ℕ} (hcount : 0 < count)
    {enlargement C : ℝ} (henlargement : 0 < enlargement) (hC : 0 < C) :
    (1 / C) * Real.log (2 * finiteCoverRangeBound count
        ((1 + enlargement) / Real.sqrt C)) =
      Real.log (16 * (count : ℝ)) / C -
        Real.pi ^ 2 / (2 *
          (((1 + 3 / (count : ℝ)) * (1 + enlargement)) ^ 2)) := by
  have hcountCast : (count : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcount.ne'
  have hspec := finiteCoverCorridorExponential_diffusive
    hcount henlargement hC
  rw [finiteCoverRangeBound, hspec]
  let q : ℝ := Real.exp
    (-(Real.pi ^ 2 / (2 *
      (((1 + 3 / (count : ℝ)) * (1 + enlargement)) ^ 2)) * C))
  have hconst : 16 * (count : ℝ) ≠ 0 := by positivity
  have hq : q ≠ 0 := by
    dsimp [q]
    exact Real.exp_ne_zero _
  have hmul : 2 * ((count : ℝ) * (8 * q)) =
      (16 * (count : ℝ)) * q := by ring
  change (1 / C) * Real.log (2 * ((count : ℝ) * (8 * q))) = _
  rw [hmul, Real.log_mul hconst hq, Real.log_exp]
  field_simp [hC.ne']
  ring

/-- The cover count and Donsker enlargement can be fixed first, after which a
sufficiently large diffusive block gives the sharp horizontal upper exponent.
This is the parameter-selection step in the corrected nested-limit route. -/
theorem exists_finiteCover_parameters_for_sharp_rate
    {ε : ℝ} (hε : 0 < ε) :
    ∃ count : ℕ, 0 < count ∧ ∃ enlargement C : ℝ,
      0 < enlargement ∧ 0 < C ∧
      finiteCoverCorridorExponential count
        ((1 + enlargement) / Real.sqrt C) < 1 / 2 ∧
      finiteCoverRangeBound count
        ((1 + enlargement) / Real.sqrt C) < 1 / 2 ∧
      (1 / C) * Real.log (2 * finiteCoverRangeBound count
        ((1 + enlargement) / Real.sqrt C)) < -(Real.pi ^ 2) / 2 + ε := by
  let denominator : ℕ → ℝ := fun j => (j : ℝ) + 1
  let reciprocal : ℕ → ℝ := fun j => (denominator j)⁻¹
  let coverFactor : ℕ → ℝ := fun j =>
    (1 + 3 * reciprocal j) * (1 + reciprocal j)
  let spectralRate : ℕ → ℝ := fun j =>
    Real.pi ^ 2 / (2 * (coverFactor j) ^ 2)
  have hdenominatorTop : Tendsto denominator atTop atTop := by
    simpa [denominator] using
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hreciprocal : Tendsto reciprocal atTop (nhds 0) := by
    change Tendsto (fun j : ℕ => (denominator j)⁻¹) atTop (nhds 0)
    exact tendsto_inv_atTop_zero.comp hdenominatorTop
  have hleft : Tendsto (fun j : ℕ => 1 + 3 * reciprocal j)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hreciprocal)
  have hright : Tendsto (fun j : ℕ => 1 + reciprocal j)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hreciprocal
  have hcoverFactor : Tendsto coverFactor atTop (nhds 1) := by
    simpa [coverFactor] using hleft.mul hright
  have hrate : Tendsto spectralRate atTop (nhds (Real.pi ^ 2 / 2)) := by
    have hcontinuous : ContinuousAt
        (fun x : ℝ => Real.pi ^ 2 / (2 * x ^ 2)) 1 := by
      apply ContinuousAt.div₀ continuousAt_const
      · fun_prop
      · norm_num
    simpa [Function.comp_def, spectralRate] using
      hcontinuous.tendsto.comp hcoverFactor
  let slack : ℝ := min (ε / 4) (Real.pi ^ 2 / 8)
  have hslackPos : 0 < slack := by
    dsimp [slack]
    exact lt_min (by positivity) (by positivity)
  have hslackEps : slack ≤ ε / 4 := min_le_left _ _
  have hrateEvent : ∀ᶠ j : ℕ in atTop,
      Real.pi ^ 2 / 2 - slack < spectralRate j := by
    have htarget : Real.pi ^ 2 / 2 - slack < Real.pi ^ 2 / 2 := by
      linarith
    filter_upwards [hrate.eventually (Ioi_mem_nhds htarget)] with j hj
    exact hj
  obtain ⟨j, hj⟩ := hrateEvent.exists
  let count : ℕ := j + 1
  let enlargement : ℝ := reciprocal j
  have hcount : 0 < count := by
    dsimp [count]
    omega
  have hcountCast : (count : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcount.ne'
  have henlargement : 0 < enlargement := by
    dsimp [enlargement, reciprocal, denominator]
    positivity
  have hchosenRate : spectralRate j = Real.pi ^ 2 / (2 *
      (((1 + 3 / (count : ℝ)) * (1 + enlargement)) ^ 2)) := by
    dsimp [spectralRate, coverFactor, reciprocal, denominator,
      enlargement, count]
    rw [Nat.cast_add, Nat.cast_one]
    have hden : (↑j : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hden]
  have hchosenRatePos : 0 < spectralRate j := by
    rw [hchosenRate]
    positivity
  let diffusiveIndex : ℕ → ℝ := fun c => (c : ℝ) + 1
  have hdiffusiveIndexTop : Tendsto diffusiveIndex atTop atTop := by
    simpa [diffusiveIndex] using
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlinear : Tendsto (fun c : ℕ => spectralRate j * diffusiveIndex c)
      atTop atTop := hdiffusiveIndexTop.const_mul_atTop hchosenRatePos
  have hexponent : Tendsto (fun c : ℕ =>
      Real.exp (-(spectralRate j * diffusiveIndex c))) atTop (nhds 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinear using 1
    funext c
    rfl
  have hreciprocalIndex : Tendsto (fun c : ℕ => (diffusiveIndex c)⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hdiffusiveIndexTop
  have hprefactor : Tendsto (fun c : ℕ =>
      Real.log (16 * (count : ℝ)) * (diffusiveIndex c)⁻¹)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hreciprocalIndex
  have hexpSmall : ∀ᶠ c : ℕ in atTop,
      Real.exp (-(spectralRate j * diffusiveIndex c)) <
        1 / (16 * (count : ℝ)) :=
    hexponent.eventually (Iio_mem_nhds (by positivity))
  have hprefSmall : ∀ᶠ c : ℕ in atTop,
      Real.log (16 * (count : ℝ)) * (diffusiveIndex c)⁻¹ < ε / 2 :=
    hprefactor.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨c, hc⟩ := (hexpSmall.and hprefSmall).exists
  let C : ℝ := diffusiveIndex c
  have hC : 0 < C := by
    dsimp [C, diffusiveIndex]
    positivity
  have hselectedExp : Real.exp (-(spectralRate j * C)) <
      1 / (16 * (count : ℝ)) := by
    simpa [C] using hc.1
  have hthreshold : 1 / (16 * (count : ℝ)) < 1 / 2 := by
    have hcountOne : (1 : ℝ) ≤ count := by exact_mod_cast hcount
    apply one_div_lt_one_div_of_lt (by norm_num)
    nlinarith
  have hchosenSpectral : finiteCoverCorridorExponential count
      ((1 + enlargement) / Real.sqrt C) < 1 / 2 := by
    rw [finiteCoverCorridorExponential_diffusive hcount henlargement hC,
      ← hchosenRate]
    exact hselectedExp.trans hthreshold
  have hchosenBoundFormula : finiteCoverRangeBound count
      ((1 + enlargement) / Real.sqrt C) =
      (count : ℝ) * (8 * Real.exp (-(spectralRate j * C))) := by
    rw [finiteCoverRangeBound,
      finiteCoverCorridorExponential_diffusive hcount henlargement hC,
      ← hchosenRate]
  have hchosenBound : finiteCoverRangeBound count
      ((1 + enlargement) / Real.sqrt C) < 1 / 2 := by
    rw [hchosenBoundFormula]
    calc
      (count : ℝ) * (8 * Real.exp (-(spectralRate j * C))) <
      (count : ℝ) * (8 * (1 / (16 * (count : ℝ)))) := by
        apply mul_lt_mul_of_pos_left
        · exact mul_lt_mul_of_pos_left hselectedExp (by norm_num)
        · positivity
      _ = 1 / 2 := by
        field_simp [hcountCast]
        ring
  have hselectedPrefactor :
      Real.log (16 * (count : ℝ)) / C < ε / 2 := by
    have h := hc.2
    simpa [C, diffusiveIndex, div_eq_mul_inv] using h
  have hlog := scaledLog_two_finiteCoverRangeBound_diffusive
    hcount henlargement hC
  rw [← hchosenRate] at hlog
  refine ⟨count, hcount, enlargement, C, henlargement, hC,
    hchosenSpectral, hchosenBound, ?_⟩
  rw [hlog]
  have hrateLower : Real.pi ^ 2 / 2 - slack < spectralRate j := hj
  calc
    Real.log (16 * (count : ℝ)) / C - spectralRate j <
        ε / 2 - (Real.pi ^ 2 / 2 - slack) := by
      linarith
    _ ≤ -(Real.pi ^ 2) / 2 + ε := by
      dsimp [slack]
      have hε : ε / 2 + min (ε / 4) (Real.pi ^ 2 / 8) ≤ ε := by
        linarith [min_le_left (ε / 4) (Real.pi ^ 2 / 8)]
      linarith

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end

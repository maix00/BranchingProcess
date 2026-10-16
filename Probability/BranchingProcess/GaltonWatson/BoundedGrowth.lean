/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Probability.BranchingProcess.GaltonWatson.Growth

/-!
# Fixed-horizon growth for bounded offspring

Every finite-slot offspring law has a finite second factorial moment.  The
generation recursions therefore give a positive Paley--Zygmund lower bound at
the logarithmic horizon, without imposing a second-moment assumption on any
larger offspring law from which the finite-slot law may have been selected.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingProcess.GaltonWatson

private theorem offspringSlotWeight_le_one {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (i : ι) : offspringSlotWeight μ i ≤ 1 := by
  classical
  unfold offspringSlotWeight
  calc
    _ ≤ ∫⁻ _ : Combinatorics.Branching.Step ι PUnit.{1},
        (1 : ℝ≥0∞) ∂(μ : Measure _) := by
      apply lintegral_mono_ae
      filter_upwards [] with ξ
      by_cases hi : Combinatorics.Branching.survive ξ i <;> simp [hi]
    _ = 1 := by simp

private theorem offspringSlotPairWeight_le_one {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (i j : ι) : offspringSlotPairWeight μ i j ≤ 1 := by
  classical
  unfold offspringSlotPairWeight
  calc
    _ ≤ ∫⁻ _ : Combinatorics.Branching.Step ι PUnit.{1},
        (1 : ℝ≥0∞) ∂(μ : Measure _) := by
      apply lintegral_mono_ae
      filter_upwards [] with ξ
      by_cases hi : Combinatorics.Branching.survive ξ i <;>
        by_cases hj : Combinatorics.Branching.survive ξ j <;> simp [hi, hj]
    _ = 1 := by simp

private theorem offspringMean_lt_top {ι : Type*} [Fintype ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) : offspringMean μ < ∞ := by
  rw [offspringMean]
  refine ENNReal.sum_lt_top.mpr fun i hi => ?_
  exact lt_of_le_of_lt (offspringSlotWeight_le_one μ i) (by simp)

private theorem offspringSecondFactorialMoment_lt_top {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) : offspringSecondFactorialMoment μ < ∞ := by
  rw [offspringSecondFactorialMoment]
  refine ENNReal.sum_lt_top.mpr fun i hi => ?_
  refine ENNReal.sum_lt_top.mpr fun j hj => ?_
  by_cases hij : i = j
  · simp [hij]
  · simpa [hij] using
      (lt_of_le_of_lt (offspringSlotPairWeight_le_one μ i j) (by simp))

private theorem generationSecondMoment_zero {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) : generationSecondMoment μ 0 = 1 := by
  rw [generationSecondMoment]
  simp [Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize_zero]

/-- The actual Galton--Watson second moment is bounded by a fixed multiple
of the square of its mean.  The coefficient only uses the finite offspring
law's mean and second factorial moment. -/
theorem generationSecondMomentReal_le_constant_mul_firstMoment_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (hμ : μ.IsSupercritical) :
    ∀ n,
      (generationSecondMoment μ n).toReal ≤
        (1 + (offspringSecondFactorialMoment μ).toReal /
          ((offspringMean μ).toReal * ((offspringMean μ).toReal - 1))) *
          (generationFirstMoment μ n).toReal ^ 2 := by
  let ρ : ℝ := (offspringMean μ).toReal
  let c : ℝ := (offspringSecondFactorialMoment μ).toReal
  let C : ℝ := 1 + c / (ρ * (ρ - 1))
  have hmean_gt : 1 < offspringMean μ := by
    rw [offspringMean_eq_expectedChildCount]
    exact hμ
  have hρ : 1 < ρ := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top
      (offspringMean_lt_top μ).ne).2 hmean_gt
    simpa [ρ] using h
  have hρpos : 0 < ρ := by linarith
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact ENNReal.toReal_nonneg
  have hfactorial_top := offspringSecondFactorialMoment_lt_top μ
  have hfactorial_toReal :
      (offspringSecondFactorialMoment μ).toReal = c := rfl
  have hmean_toReal : (offspringMean μ).toReal = ρ := rfl
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hcoeff : ρ * C + c ≤ C * ρ ^ 2 := by
    have hden : ρ * (ρ - 1) ≠ 0 :=
      (mul_pos hρpos (sub_pos.mpr hρ)).ne'
    have hsub : ρ - 1 ≠ 0 := (sub_pos.mpr hρ).ne'
    have heq : C * ρ ^ 2 - ρ * C - c = ρ * (ρ - 1) := by
      dsimp [C]
      field_simp [hden, hρpos.ne', hsub]
      ring
    linarith [heq, mul_pos hρpos (sub_pos.mpr hρ)]
  have hfirst (n : ℕ) :
      (generationFirstMoment μ n).toReal = ρ ^ n := by
    rw [generationFirstMoment_eq_offspringMean_pow]
    simp [ρ, ENNReal.toReal_pow]
  have hsecondRec (n : ℕ) :
      (generationSecondMoment μ (n + 1)).toReal =
        ρ * (generationSecondMoment μ n).toReal + c * ρ ^ (2 * n) := by
    rw [generationSecondMomentReal_succ_eq_offspringMoments μ n, hfirst]
    have hp : (ρ ^ n) ^ 2 = ρ ^ (2 * n) := by
      rw [← pow_mul, Nat.mul_comm n 2]
    simpa [ρ, c, hp]
  have hsecond_pos (n : ℕ) : 0 < (generationSecondMoment μ n).toReal := by
    have hlow : ρ ^ n ≤ (generationSecondMoment μ n).toReal := by
      induction n with
      | zero => rw [generationSecondMoment_zero]; simp
      | succ n ih =>
          rw [hsecondRec]
          calc
            ρ ^ (n + 1) = ρ * ρ ^ n := by rw [pow_succ]; ring
            _ ≤ ρ * (generationSecondMoment μ n).toReal :=
              mul_le_mul_of_nonneg_left ih (le_of_lt hρpos)
            _ ≤ ρ * (generationSecondMoment μ n).toReal +
                c * ρ ^ (2 * n) :=
              le_add_of_nonneg_right
                (mul_nonneg hc_nonneg (pow_nonneg hρpos.le _))
    exact lt_of_lt_of_le (pow_pos hρpos _) hlow
  have hbound : ∀ n,
      (generationSecondMoment μ n).toReal ≤ C * ρ ^ (2 * n) := by
    intro n
    induction n with
    | zero =>
        have hdenpos : 0 < ρ * (ρ - 1) :=
          mul_pos hρpos (sub_pos.mpr hρ)
        have hC_ge_one : 1 ≤ C := by
          dsimp [C]
          exact le_add_of_nonneg_right (div_nonneg hc_nonneg hdenpos.le)
        rw [generationSecondMoment_zero]
        simpa using hC_ge_one
    | succ n ih =>
        rw [hsecondRec]
        calc
          ρ * (generationSecondMoment μ n).toReal + c * ρ ^ (2 * n) ≤
              ρ * (C * ρ ^ (2 * n)) + c * ρ ^ (2 * n) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left ih hρpos.le) le_rfl
          _ = (ρ * C + c) * ρ ^ (2 * n) := by ring
          _ ≤ (C * ρ ^ 2) * ρ ^ (2 * n) :=
            mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hρpos.le _)
          _ = C * ρ ^ (2 * (n + 1)) := by
            rw [Nat.mul_succ, pow_add]
            ring
  intro n
  have hp : ρ ^ (2 * n) = (ρ ^ n) ^ 2 := by
    rw [show 2 * n = n * 2 by omega, pow_mul]
  change (generationSecondMoment μ n).toReal ≤
    (1 + (offspringSecondFactorialMoment μ).toReal /
      ((offspringMean μ).toReal * ((offspringMean μ).toReal - 1))) *
      (generationFirstMoment μ n).toReal ^ 2
  calc
    (generationSecondMoment μ n).toReal ≤ C * ρ ^ (2 * n) := hbound n
    _ = C * (generationFirstMoment μ n).toReal ^ 2 := by
      rw [hfirst n, hp]
    _ = (1 + (offspringSecondFactorialMoment μ).toReal /
        ((offspringMean μ).toReal * ((offspringMean μ).toReal - 1))) *
        (generationFirstMoment μ n).toReal ^ 2 := by
      rfl

/-- At the logarithmic horizon, a finite-slot supercritical Galton--Watson
population reaches the prescribed power scale with a uniform positive
probability.  The finite-slot bound supplies all moments used here; no
moment assumption on an untruncated offspring law is needed. -/
theorem measure_generation_ge_floor_rpow_of_supercritical_finite_slots
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (hμ : μ.IsSupercritical)
    (N : ℕ) (a : ℝ) (hN : 1 ≤ N) :
    ((law μ : ProbabilityMeasure (Combinatorics.Branching.Process ι)).toMeasure.real
      {β | (⌊(N : ℝ) ^ a⌋₊ : ℝ) ≤
        generationSizeReal
          ⌈(a * Real.log N + Real.log 2) /
            Real.log ((offspringMean μ).toReal)⌉₊ β}) ≥
      1 / (4 * (1 + (offspringSecondFactorialMoment μ).toReal /
        ((offspringMean μ).toReal * ((offspringMean μ).toReal - 1)))) := by
  let ρ : ℝ := (offspringMean μ).toReal
  let c : ℝ := (offspringSecondFactorialMoment μ).toReal
  let C : ℝ := 1 + c / (ρ * (ρ - 1))
  have hmean_gt : 1 < offspringMean μ := by
    rw [offspringMean_eq_expectedChildCount]
    exact hμ
  have hρ : 1 < ρ := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top
      (offspringMean_lt_top μ).ne).2 hmean_gt
    simpa [ρ] using h
  have hρpos : 0 < ρ := by linarith
  have hCpos : 0 < C := by
    have hdenpos : 0 < ρ * (ρ - 1) :=
      mul_pos hρpos (sub_pos.mpr hρ)
    have hc_nonneg : 0 ≤ c := by
      dsimp [c]
      exact ENNReal.toReal_nonneg
    have hC_ge_one : 1 ≤ C := by
      dsimp [C]
      exact le_add_of_nonneg_right (div_nonneg hc_nonneg hdenpos.le)
    linarith
  have hmean_pos (n : ℕ) : 0 < (generationFirstMoment μ n).toReal := by
    rw [generationFirstMoment_eq_offspringMean_pow]
    simpa [ρ, ENNReal.toReal_pow] using pow_pos hρpos n
  have hfirst (n : ℕ) :
      (generationFirstMoment μ n).toReal = ρ ^ n := by
    rw [generationFirstMoment_eq_offspringMean_pow]
    simp [ρ, ENNReal.toReal_pow]
  have hrec (n : ℕ) :
      (generationSecondMoment μ (n + 1)).toReal =
        ρ * (generationSecondMoment μ n).toReal + c * ρ ^ (2 * n) := by
    rw [generationSecondMomentReal_succ_eq_offspringMoments μ n, hfirst]
    have hp : (ρ ^ n) ^ 2 = ρ ^ (2 * n) := by
      rw [← pow_mul, Nat.mul_comm n 2]
    simpa [ρ, c, hp]
  have hsecond_pos (n : ℕ) : 0 < (generationSecondMoment μ n).toReal := by
    have hlow : ∀ n,
        ρ ^ n ≤ (generationSecondMoment μ n).toReal := by
      intro n
      induction n with
      | zero => rw [generationSecondMoment_zero]; simp
      | succ n ih =>
          rw [hrec]
          calc
            ρ ^ (n + 1) = ρ * ρ ^ n := by rw [pow_succ]; ring
            _ ≤ ρ * (generationSecondMoment μ n).toReal :=
              mul_le_mul_of_nonneg_left ih hρpos.le
            _ ≤ ρ * (generationSecondMoment μ n).toReal + c * ρ ^ (2 * n) :=
              le_add_of_nonneg_right
                (mul_nonneg (by dsimp [c]; exact ENNReal.toReal_nonneg)
                  (pow_nonneg hρpos.le _))
    exact lt_of_lt_of_le (pow_pos hρpos _) (hlow n)
  have hsecond_le (n : ℕ) :
      (generationSecondMoment μ n).toReal ≤
        C * (generationFirstMoment μ n).toReal ^ 2 := by
    simpa [C, c, ρ] using
      generationSecondMomentReal_le_constant_mul_firstMoment_sq μ hμ n
  let h : ℕ :=
    ⌈(a * Real.log N + Real.log 2) / Real.log ρ⌉₊
  have hscale :
      2 * (⌊(N : ℝ) ^ a⌋₊ : ℝ) ≤ ρ ^ h := by
    have hfloor : (⌊(N : ℝ) ^ a⌋₊ : ℝ) ≤ (N : ℝ) ^ a :=
      Nat.floor_le (Real.rpow_nonneg (by positivity : 0 ≤ (N : ℝ)) a)
    have hpow := rho_pow_ceil_log_ge_two_mul_rpow ρ a N hρ hN
    dsimp [h]
    exact (mul_le_mul_of_nonneg_left hfloor (by norm_num)).trans hpow
  have hhalf := measure_generationSizeReal_ge_half_mean_of_secondMoment_le
    μ h C (hmean_pos h) (hsecond_pos h) hCpos (hsecond_le h)
  have hsubset :
      {β : Combinatorics.Branching.Process ι |
        (generationFirstMoment μ h).toReal / 2 ≤ generationSizeReal h β} ⊆
      {β | (⌊(N : ℝ) ^ a⌋₊ : ℝ) ≤ generationSizeReal h β} := by
    intro β hβ
    have hfirst : (generationFirstMoment μ h).toReal = ρ ^ h := by
      rw [generationFirstMoment_eq_offspringMean_pow]
      simp [ρ, ENNReal.toReal_pow]
    rw [hfirst] at hβ
    exact (by linarith : (⌊(N : ℝ) ^ a⌋₊ : ℝ) ≤ ρ ^ h / 2).trans hβ
  have hresult :
      ((law μ : ProbabilityMeasure (Combinatorics.Branching.Process ι)).toMeasure.real
        {β | (⌊(N : ℝ) ^ a⌋₊ : ℝ) ≤ generationSizeReal h β}) ≥ 1 / (4 * C) := by
    calc
      _ ≥ ((law μ : ProbabilityMeasure (Combinatorics.Branching.Process ι)).toMeasure.real
          {β | (generationFirstMoment μ h).toReal / 2 ≤ generationSizeReal h β}) :=
        measureReal_mono hsubset
      _ ≥ 1 / (4 * C) := hhalf
  simpa [h, C, c, ρ] using hresult

end ProbabilityTheory.BranchingProcess.GaltonWatson

end

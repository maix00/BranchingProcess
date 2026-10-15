/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.FiniteVarianceSurvivalLower
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Transition

/-!
# Finite-variance survival at a diffusive horizon

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_diffusiveSurvivalProbability_ge_power_of_centeredSecondMoment`:
  if $\Delta_n\to\infty$ and
  $N_n=\lfloor\Delta_n^2\rfloor-m$, then centered increments with
  variance $\sigma^2>0$ satisfy
  $\mathbb P(C_{N_n})\ge C\Delta_n^{-(1+\alpha)}$ eventually,
  for each $\alpha>0$ and some $C>0$.

The proof applies the finite-variance survival lower bound obtained from
M. Bauer, C. Godrèche, and J.-M. Luck, *Statistics of persistent events
in the binomial random walk: Will the drunken sailor hit the sober man?*,
Appendix A, equation (A.7) (arXiv:cond-mat/9905252), at the diffusive horizon.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

/-- The diffusive-horizon survival factor in the transition estimate of
Wang Yiyang, Appendix A.2, obtained from the finite coefficient recurrence. -/
theorem exists_eventually_diffusiveSurvivalProbability_ge_power_of_centeredSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {alpha : ℝ} (halpha : 0 < alpha)
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    (offset : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C / width n ^ (1 + alpha) ≤
        ((iidSequenceLaw ν)
          {increment | SurvivesNonnegative
            (diffusiveTransitionHorizon width offset n) increment}).toReal := by
  let γ : ℝ := 1 / (2 * (1 + alpha))
  let δ : ℝ := 1 - γ
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγhalf : γ < 1 / 2 := by
    dsimp [γ]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (1 + alpha))).2
    nlinarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hexponent : 2 * δ ≤ 1 + alpha := by
    dsimp [δ, γ]
    have hp : 0 < 2 * (1 + alpha) := by positivity
    field_simp
    nlinarith [sq_nonneg alpha]
  obtain ⟨C, hC, hsurv⟩ :=
    RandomWalk.exists_nonnegativeSurvivalProbability_ge_power_of_centeredSecondMoment
      ν hν hsigma hγ hγhalf
  let D : ℝ := C / (2 : ℝ) ^ δ
  have hD : 0 < D := div_pos hC (by positivity)
  refine ⟨D, hD, ?_⟩
  filter_upwards [hwidth.eventually (eventually_ge_atTop 1)] with n hn
  let N : ℕ := diffusiveTransitionHorizon width offset n
  have hNbound : ((N + 1 : ℕ) : ℝ) ≤ 2 * width n ^ 2 := by
    have hfloor : (Nat.floor (width n ^ 2) : ℝ) ≤ width n ^ 2 :=
      Nat.floor_le (sq_nonneg _)
    have hsub : N ≤ Nat.floor (width n ^ 2) := Nat.sub_le _ _
    have hone : (1 : ℝ) ≤ width n ^ 2 := by nlinarith
    have hsubR : (N : ℝ) ≤ (Nat.floor (width n ^ 2) : ℝ) := by
      exact_mod_cast hsub
    push_cast
    nlinarith
  have hNpos : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
  have hwidthpos : 0 < width n := by linarith
  have hbasepos : 0 < 2 * width n ^ 2 := by positivity
  have hpowbound : (((N + 1 : ℕ) : ℝ) ^ δ) ≤
      (2 : ℝ) ^ δ * width n ^ (2 * δ) := by
    calc
      _ ≤ (2 * width n ^ 2) ^ δ :=
        Real.rpow_le_rpow hNpos.le hNbound hδ.le
      _ = (2 : ℝ) ^ δ * (width n ^ 2) ^ δ := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
      _ = _ := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hwidthpos.le]
        congr 1
  have hpowα : width n ^ (2 * δ) ≤ width n ^ (1 + alpha) :=
    Real.rpow_le_rpow_of_exponent_le hn hexponent
  have hsurvN := hsurv N
  have hpoweq : (((N + 1 : ℕ) : ℝ) ^ (γ - 1)) =
      1 / (((N + 1 : ℕ) : ℝ) ^ δ) := by
    rw [show γ - 1 = -δ by dsimp [δ]; ring]
    rw [Real.rpow_neg hNpos.le]
    ring
  rw [hpoweq] at hsurvN
  have hpowD : 0 < (2 : ℝ) ^ δ * width n ^ (1 + alpha) := by positivity
  have hpowN : 0 < (((N + 1 : ℕ) : ℝ) ^ δ) := by positivity
  have hdiv : D / width n ^ (1 + alpha) ≤
      C / (((N + 1 : ℕ) : ℝ) ^ δ) := by
    dsimp [D]
    rw [← div_mul_eq_div_div]
    apply (div_le_div_iff₀ hpowD hpowN).2
    have hdenLe := hpowbound.trans
      (mul_le_mul_of_nonneg_left hpowα (by positivity : 0 ≤ (2 : ℝ) ^ δ))
    exact mul_le_mul_of_nonneg_left hdenLe hC.le
  exact hdiv.trans (by simpa only [one_div, one_mul, div_eq_mul_inv, N] using hsurvN)

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end

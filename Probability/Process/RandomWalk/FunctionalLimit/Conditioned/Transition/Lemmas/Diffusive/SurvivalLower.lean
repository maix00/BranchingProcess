/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Rotation.Probability
public import Probability.Process.RandomWalk.Fluctuation.FiniteVarianceSignLimit
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Transition.Event

/-!
# Finite-variance survival at a diffusive horizon

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_diffusiveSurvivalProbability_ge_inverse_square_of_centeredSecondMoment`:
  for centered increments of variance $\sigma^2>0$ and
  $N_n=\lfloor\Delta_n^2\rfloor-m$, there is $C>0$ such that
  $\mathbb P(C_{N_n})\ge C\Delta_n^{-2}$ eventually.

The proof combines the cyclic rotation inequality of
Bauer--Godrèche--Luck, *Statistics of persistent events in the binomial
random walk: Will the drunken sailor hit the sober man?*, Appendix A,
immediately after (A.3) (arXiv:cond-mat/9905252), with the Gaussian
endpoint-sign limit.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

/-- At a diffusive horizon, the cyclic-rotation survival bound and the
Gaussian endpoint-sign limit give an inverse-square width bound. -/
theorem exists_eventually_diffusiveSurvivalProbability_ge_inverse_square_of_centeredSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    (offset : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C / width n ^ 2 ≤
        ((iidSequenceLaw ν)
          {increment | SurvivesNonnegative
            (diffusiveTransitionHorizon width offset n) increment}).toReal := by
  let N := diffusiveTransitionHorizon width offset
  have hargument : Tendsto (fun n => width n ^ 2) atTop atTop := by
    have hmul : Tendsto (fun n => width n * width n) atTop atTop :=
      hwidth.atTop_mul_atTop₀ hwidth
    simpa [pow_two] using hmul
  have hN : Tendsto N atTop atTop := by
    change Tendsto (fun n =>
      Asymptotics.floorBlockLength (fun k => width k ^ 2) n - offset)
      atTop atTop
    exact (tendsto_sub_atTop_nat offset).comp
      (Asymptotics.tendsto_floorBlockLength_atTop hargument)
  have hendpoint : Tendsto (fun n : ℕ =>
      ((iidSequenceLaw ν)
        {increment | 0 ≤ AdditivePath.displacement n increment}).toReal)
        atTop (nhds (1 / 2 : ℝ)) := by
    have h := RandomWalk.tendsto_nonnegativePartialSumProbability_half ν hν hsigma
    have hreal := (ENNReal.tendsto_toReal (by norm_num :
      (1 / 2 : ℝ≥0∞) ≠ ⊤)).comp h
    simpa only [Function.comp_def,
      show (1 / 2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) by norm_num] using hreal
  have hpositive : ∀ᶠ n : ℕ in atTop,
      (1 / 4 : ℝ) ≤ ((iidSequenceLaw ν)
        {increment | 0 ≤ AdditivePath.displacement n increment}).toReal := by
    exact (hendpoint.eventually (eventually_gt_nhds
      (show (1 / 4 : ℝ) < 1 / 2 by norm_num))).mono
      (by intro n hn; exact hn.le)
  refine ⟨1 / 4, by norm_num, ?_⟩
  filter_upwards [hN.eventually (eventually_gt_atTop 0),
    hN.eventually hpositive,
    hwidth.eventually (eventually_gt_atTop 0)] with n hn hsign hwidthpos
  have hrot := RandomWalk.measure_nonnegativeEndpoint_le_card_mul_survival ν hn
  have hrotReal :
      ((iidSequenceLaw ν)
        {increment | 0 ≤ AdditivePath.displacement (N n) increment}).toReal ≤
      (N n : ℝ) * ((iidSequenceLaw ν)
        {increment | SurvivesNonnegative (N n) increment}).toReal := by
    have hfinite : (iidSequenceLaw ν)
        {increment | SurvivesNonnegative (N n) increment} ≠ ⊤ :=
      measure_ne_top _ _
    have h := ENNReal.toReal_mono (by
      simpa only [nsmul_eq_mul] using
        (ENNReal.mul_ne_top (by simp : (N n : ℝ≥0∞) ≠ ⊤) hfinite)) hrot
    simpa only [nsmul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_natCast] using h
  have hNbound : (N n : ℝ) ≤ width n ^ 2 := by
    have hsub : N n ≤ Nat.floor (width n ^ 2) := Nat.sub_le _ _
    have hfloor : (Nat.floor (width n ^ 2) : ℝ) ≤ width n ^ 2 :=
      Nat.floor_le (sq_nonneg _)
    have hsubR : (N n : ℝ) ≤ (Nat.floor (width n ^ 2) : ℝ) := by
      exact_mod_cast hsub
    exact hsubR.trans hfloor
  have hsurvNonneg : 0 ≤ ((iidSequenceLaw ν)
      {increment | SurvivesNonnegative (N n) increment}).toReal :=
    ENNReal.toReal_nonneg
  have hwidthsq : 0 < width n ^ 2 := sq_pos_of_pos hwidthpos
  apply (div_le_iff₀ hwidthsq).2
  calc
    (1 / 4 : ℝ) ≤ ((iidSequenceLaw ν)
        {increment | 0 ≤ AdditivePath.displacement (N n) increment}).toReal :=
      hsign
    _ ≤ (N n : ℝ) * ((iidSequenceLaw ν)
        {increment | SurvivesNonnegative (N n) increment}).toReal := hrotReal
    _ ≤ width n ^ 2 * ((iidSequenceLaw ν)
        {increment | SurvivesNonnegative (N n) increment}).toReal :=
      mul_le_mul_of_nonneg_right hNbound hsurvNonneg
    _ = ((iidSequenceLaw ν)
        {increment | SurvivesNonnegative
          (diffusiveTransitionHorizon width offset n) increment}).toReal *
        width n ^ 2 := by rw [mul_comm]

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end

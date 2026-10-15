/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Transition
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.TransitionDiffusiveFromMeander
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.SurvivalPower

/-!
# Diffusive entrance bound from survival and the meander limit

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_diffusiveTransitionProbability_ge_power_of_conditionalBound`:
  combine a conditional transition lower bound and a survival lower bound.

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_diffusiveTransitionProbability_ge_power_of_centeredSecondMoment`:
  the same bound with the meander limit and its support supplied by the
  centered finite-variance hypotheses; survival regular variation remains
  explicit.

This is the multiplication step in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Appendix A.2, first lemma. The survival asymptotic is Caravenna--Chaumont,
*Invariance principles for random walks conditioned to stay positive*,
Lemma 2.1; the conditioned path limit is recalled in their equation (3.3).
Chaumont--Doney, *Invariance principles for local times at the maximum of
random walks and Lévy processes*, Theorem 6 (DOI 10.1214/09-AOP512),
provides a later treatment of the meander limit.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

/-- Combine the two factors in
$\mathbb P(D_{N,\Delta})
 =\mathbb P(D_{N,\Delta}\mid C_N)\mathbb P(C_N)$
at the diffusive horizon. This implements the corresponding step in
Wang Yiyang, Appendix A.2, first lemma. -/
theorem exists_eventually_diffusiveTransitionProbability_ge_power_of_conditionalBound
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (hreg : Asymptotics.IsRegularlyVaryingAtTop
      (survivalProbabilityReal ν) (-(1 / 2 : ℝ)))
    {alpha : ℝ} (halpha : 0 < alpha)
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    (offset : ℕ)
    [∀ n, IsProbabilityMeasure
      (survivalConditionedLaw ν (diffusiveTransitionHorizon width offset n))]
    (htransition : ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      q ≤ survivalConditionedLaw ν
        (diffusiveTransitionHorizon width offset n)
        (nonnegativeTransitionEvent
          (diffusiveTransitionHorizon width offset n) (width n))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C / width n ^ (1 + alpha) ≤
        (iidSequenceLaw ν
          (nonnegativeTransitionEvent
            (diffusiveTransitionHorizon width offset n) (width n))).toReal := by
  obtain ⟨q, hq, hconditional⟩ := htransition
  obtain ⟨C, hC, hsurvival⟩ :=
    exists_eventually_diffusiveSurvivalProbability_ge_power
      ν hν hsigma hreg halpha hwidth offset
  have hqfinite : (min q 1) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (min_le_right q 1) (by simp))
  have hqmin : (0 : ℝ≥0∞) < min q 1 :=
    lt_min hq (by norm_num)
  have hqpositive : 0 < (min q 1).toReal :=
    ENNReal.toReal_pos hqmin.ne' hqfinite
  refine ⟨(min q 1).toReal * C, mul_pos hqpositive hC, ?_⟩
  filter_upwards [hconditional, hsurvival,
    hwidth.eventually (eventually_gt_atTop 0)] with n hcond hsurv hw
  have hcondReal : (min q 1).toReal ≤
      (survivalConditionedLaw ν
        (diffusiveTransitionHorizon width offset n)
        (nonnegativeTransitionEvent
          (diffusiveTransitionHorizon width offset n) (width n))).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) ((min_le_left _ _).trans hcond)
  have hsurvNonneg : 0 ≤
      ((iidSequenceLaw ν)
        {increment | SurvivesNonnegative
          (diffusiveTransitionHorizon width offset n) increment}).toReal :=
    ENNReal.toReal_nonneg
  have hquotNonneg : 0 ≤ C / width n ^ (1 + alpha) :=
    div_nonneg hC.le (Real.rpow_nonneg hw.le _)
  have hproduct :
      (min q 1).toReal * (C / width n ^ (1 + alpha)) ≤
      (survivalConditionedLaw ν
        (diffusiveTransitionHorizon width offset n)
        (nonnegativeTransitionEvent
          (diffusiveTransitionHorizon width offset n) (width n))).toReal *
      ((iidSequenceLaw ν)
        {increment | SurvivesNonnegative
          (diffusiveTransitionHorizon width offset n) increment}).toReal :=
    mul_le_mul hcondReal hsurv hquotNonneg
      (ENNReal.toReal_nonneg)
  convert hproduct using 1
  · rw [mul_div_assoc]
  · rw [← ENNReal.toReal_mul,
      ← measure_nonnegativeTransitionEvent_eq_cond_mul_survival]

/-- The probability product bound with the conditioned meander input and
its support established from centered finite-variance increments. -/
theorem exists_eventually_diffusiveTransitionProbability_ge_power_of_centeredSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (hreg : Asymptotics.IsRegularlyVaryingAtTop
      (survivalProbabilityReal ν) (-(1 / 2 : ℝ)))
    {alpha : ℝ} (halpha : 0 < alpha)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {rho : ℝ} (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    (offset : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C / width n ^ (1 + alpha) ≤
        (iidSequenceLaw ν
          (nonnegativeTransitionEvent
            (diffusiveTransitionHorizon width offset n) (width n))).toReal := by
  letI : ∀ n : ℕ, IsProbabilityMeasure
      (survivalConditionedLaw ν (diffusiveTransitionHorizon width offset n)) :=
    fun n => survivalConditionedLaw_isProbabilityMeasure_of_centeredSecondMoment
      ν hν hsigma _
  have htransition :=
    exists_eventually_diffusiveTransitionConditionalProbability_ge_of_centeredSecondMoment
      ν hν hsigma hB hcontinuous hmeasurable hrho hrhoSmall hwidth offset
  exact exists_eventually_diffusiveTransitionProbability_ge_power_of_conditionalBound
    hν hsigma hreg halpha hwidth offset htransition

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end

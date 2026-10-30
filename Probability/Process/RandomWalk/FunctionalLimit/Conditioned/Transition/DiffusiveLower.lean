/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Transition.Event
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Survival.Conditioning
import all Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Transition.Lemmas.Diffusive.ConditionalProbability
import all Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Transition.Lemmas.Diffusive.SurvivalLower
import Probability.Process.Brownian.Construction.Existence

/-!
# Diffusive entrance bound from survival and the meander limit

## Public declarations

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_diffusiveTransitionProbability_ge_inverse_square_of_centeredFiniteVariance`:
  for centered increments of variance $\sigma^2>0$ and widths
  $\Delta_n\to\infty$, there is $C>0$ such that
  $\mathbb P(D_{N_{\Delta_n,m},\Delta_n})\ge\frac{C}{\Delta_n^2}$
  eventually, with the Brownian witness obtained from the Gaussian random-walk
  functional limit.

The conditional-product step and the version with an explicit Brownian
witness are private proof helpers.

This is the multiplication step in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(master's thesis, Fudan University, 2026),
Appendix A.2, Lemma A.7. The survival bound follows from the cyclic
rotation cover in M. Bauer,
C. Godrèche, and J.-M. Luck, *Statistics of persistent events in the
binomial random walk: Will the drunken sailor hit the sober man?*,
Appendix A, immediately after (A.3) (arXiv:cond-mat/9905252). The
conditioned path limit appears in Francesco
Caravenna and Loïc Chaumont, *Invariance principles for random walks
conditioned to stay positive*, equation (3.3) (DOI 10.1214/07-AIHP119).
Chaumont--Doney, *Invariance principles for local times at the maximum of
random walks and Lévy processes*, Theorem 6 (DOI 10.1214/09-AOP512),
provides a later treatment of the meander limit.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

/-- The transition event is contained in survival, so its probability is
the product of its survival-conditioned probability and the survival
probability. -/
private lemma measure_nonnegativeTransitionEvent_eq_cond_mul_survival
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) (width : ℝ) :
    iidSequenceLaw ν (nonnegativeTransitionEvent n width) =
      survivalConditionedLaw ν n (nonnegativeTransitionEvent n width) *
        iidSequenceLaw ν {increment | SurvivesNonnegative n increment} := by
  let C : Set (ℕ → ℝ) := {increment | SurvivesNonnegative n increment}
  let D : Set (ℕ → ℝ) := nonnegativeTransitionEvent n width
  have hsubset : D ⊆ C := by
    intro increment hin k
    exact (hin.1 k).1
  have hinter : C ∩ D = D := Set.inter_eq_right.mpr hsubset
  have hcond := ProbabilityTheory.cond_mul_eq_inter
    (measurableSet_survivesNonnegative n) D (iidSequenceLaw ν)
  simpa only [survivalConditionedLaw, C, D, hinter] using hcond.symm

/-- Combine the two factors in
$\mathbb P(D_{N,\Delta})
 =\mathbb P(D_{N,\Delta}\mid C_N)\mathbb P(C_N)$
at the diffusive horizon. This implements the corresponding step in
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (master's thesis, Fudan University, 2026), Appendix A.2,
Lemma A.7. -/
private lemma exists_eventually_diffusiveTransitionProbability_ge_inverse_square_of_conditionalBound
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
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
      C / width n ^ 2 ≤
        (iidSequenceLaw ν
          (nonnegativeTransitionEvent
            (diffusiveTransitionHorizon width offset n) (width n))).toReal := by
  obtain ⟨q, hq, hconditional⟩ := htransition
  obtain ⟨C, hC, hsurvival⟩ :=
    exists_eventually_diffusiveSurvivalProbability_ge_inverse_square_of_centeredSecondMoment
      ν hν hsigma hwidth offset
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
  have hquotNonneg : 0 ≤ C / width n ^ 2 :=
    div_nonneg hC.le (sq_nonneg _)
  have hproduct :
      (min q 1).toReal * (C / width n ^ 2) ≤
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
private lemma exists_eventually_diffusiveTransitionProbability_ge_inverse_square_of_centeredSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {rho : ℝ} (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    (offset : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C / width n ^ 2 ≤
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
  exact exists_eventually_diffusiveTransitionProbability_ge_inverse_square_of_conditionalBound
    hν hsigma hwidth offset htransition

/-- The Brownian process used in the conditioned-meander transition estimate
is supplied by the Gaussian random-walk limit and its continuous modification. -/
theorem exists_eventually_diffusiveTransitionProbability_ge_inverse_square_of_centeredFiniteVariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {rho : ℝ} (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    (offset : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C / width n ^ 2 ≤
        (iidSequenceLaw ν
          (nonnegativeTransitionEvent
            (diffusiveTransitionHorizon width offset n) (width n))).toReal := by
  obtain ⟨Q, B, hB, hmeasurable, hcontinuous⟩ := exists_brownianReal
  letI : IsProbabilityMeasure
      (Q : Measure (ℕ → CadlagPath unitInterval ℝ)) := Q.property
  exact exists_eventually_diffusiveTransitionProbability_ge_inverse_square_of_centeredSecondMoment
    ν hν hsigma hB hcontinuous hmeasurable
    hrho hrhoSmall hwidth offset

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end

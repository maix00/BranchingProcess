/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Survival.Probability
public import Probability.Sequence.IID.Basic
public import Probability.Distributions.Moments.Signs
public import Mathlib.Probability.ConditionalProbability

/-!
# Random-walk laws conditioned on nonnegative survival

The public objects and theorems in this file are:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.survivalConditionedLaw`:
  the i.i.d. increment law conditioned on
  $C_n=\{S_j\ge0:1\le j\le n\}$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.survivalConditionedLaw_isProbabilityMeasure`:
  $\mathbb P(C_n)>0$ makes the conditioned law a probability measure.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.survivalConditionedLaw_isProbabilityMeasure_of_positiveIncrement`:
  $\nu((0,\infty))>0$ makes every survival-conditioned law a probability
  measure.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.survivalConditionedLaw_isProbabilityMeasure_of_centeredUnitSecondMoment`:
  centered unit-second-moment increments supply that positivity directly.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.survivalConditionedLaw_isProbabilityMeasure_of_centeredSecondMoment`:
  centered increments with variance $\sigma^2>0$ give a probability law
  after survival conditioning at every finite horizon.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.ae_nonnegative_normalizedStepCadlagPathIcc`:
  under this conditioned law and a positive normalization, the step path
  is nonnegative at every time in $[0,1]$ almost surely.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.ae_nonnegative_normalizedLinearCadlagPathIcc`:
  under the same law, the normalized polygonal path satisfies
  $S_n^{\mathrm{lin}}(t)\ge0$ for every $t\in[0,1]$ almost surely.

The survival conditioning is the one in Francesco Caravenna and Loïc
Chaumont, *Invariance principles for random walks conditioned to stay
positive*, Ann. Inst. H. Poincaré Probab. Stat. 44(1) (2008), 170–190,
Lemma 2.1 and equation (3.3), DOI 10.1214/07-AIHP119. This file proves
the finite-path facts used by the conditioned invariance principle.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

/-- The i.i.d. real-increment law conditioned to survive through time `n`.
This is the conditional law in Francesco Caravenna and Loïc Chaumont,
*Invariance principles for random walks conditioned to stay positive*,
equation (3.3), DOI 10.1214/07-AIHP119. -/
noncomputable def survivalConditionedLaw (ν : Measure ℝ) (n : ℕ) :
    Measure (ℕ → ℝ) :=
  (iidSequenceLaw ν)[|{increment | SurvivesNonnegative n increment}]

/-- Positive survival probability normalizes the conditional law. -/
theorem survivalConditionedLaw_isProbabilityMeasure
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ)
    (hpositive : (iidSequenceLaw ν)
      {increment | SurvivesNonnegative n increment} ≠ 0) :
    IsProbabilityMeasure (survivalConditionedLaw ν n) := by
  unfold survivalConditionedLaw
  exact cond_isProbabilityMeasure hpositive

/-- A positive upper half-line for the increment law gives a probability
law after conditioning on finite survival. -/
theorem survivalConditionedLaw_isProbabilityMeasure_of_positiveIncrement
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpositive : 0 < ν (Set.Ioi 0)) (n : ℕ) :
    IsProbabilityMeasure (survivalConditionedLaw ν n) :=
  survivalConditionedLaw_isProbabilityMeasure ν n
    (ne_of_gt (survivalProbability_pos_of_positiveIncrement ν hpositive n))

/-- Centered nondegenerate unit-variance increments have positive probability
to survive every finite horizon, so their survival-conditioned law is a
probability measure. -/
theorem survivalConditionedLaw_isProbabilityMeasure_of_centeredUnitSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν) (n : ℕ) :
    IsProbabilityMeasure (survivalConditionedLaw ν n) :=
  survivalConditionedLaw_isProbabilityMeasure_of_positiveIncrement ν
    hν.measure_Ioi_zero_pos n

/-- Positive finite variance and zero mean ensure that conditioning on
nonnegative survival is well defined at every finite time. -/
theorem survivalConditionedLaw_isProbabilityMeasure_of_centeredSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) (n : ℕ) :
    IsProbabilityMeasure (survivalConditionedLaw ν n) :=
  survivalConditionedLaw_isProbabilityMeasure_of_positiveIncrement ν
    (hν.measure_Ioi_zero_pos hsigma) n

/-- Survival conditioning makes the normalized random-walk step path
nonnegative almost surely, as required for the transition event in
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5, and Appendix A.2, Lemma A.7. -/
theorem ae_nonnegative_normalizedStepCadlagPathIcc
    (ν : Measure ℝ) (n : ℕ) (scale : ℕ → ℝ)
    (hscale : 0 < scale n) :
    ∀ᵐ increment ∂survivalConditionedLaw ν n,
      ∀ t : unitInterval,
        0 ≤ normalizedStepCadlagPathIcc scale n increment t := by
  unfold survivalConditionedLaw
  exact ae_cond_of_forall_mem (measurableSet_survivesNonnegative n)
    (fun increment hsurvival =>
      hsurvival.normalizedStepCadlagPathIcc_nonnegative scale hscale)

/-- Survival conditioning also makes the polygonal interpolation
nonnegative at every time. -/
theorem ae_nonnegative_normalizedLinearCadlagPathIcc
    (ν : Measure ℝ) {n : ℕ} (hn : 0 < n) (scale : ℕ → ℝ)
    (hscale : 0 < scale n) :
    ∀ᵐ increment ∂survivalConditionedLaw ν n,
      ∀ t : unitInterval,
        0 ≤ normalizedLinearCadlagPathIcc scale n increment t := by
  unfold survivalConditionedLaw
  exact ae_cond_of_forall_mem (measurableSet_survivesNonnegative n)
    (fun increment hsurvival =>
      hsurvival.normalizedLinearCadlagPathIcc_nonnegative scale hn hscale)

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end

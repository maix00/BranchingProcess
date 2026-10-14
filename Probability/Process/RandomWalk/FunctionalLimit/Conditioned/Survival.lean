/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Survival
public import Probability.Sequence.IID
public import Probability.Distributions.Moments.Signs
public import Mathlib.Probability.ConditionalProbability

/-!
# Random-walk laws conditioned on nonnegative survival

The public objects and theorems in this file are:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.survivalConditionedLaw`:
  the i.i.d. increment law conditioned on
  $C_n=\{S_j\ge0:1\le j\le n\}$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.survivalProbability_pos_of_positiveIncrement`:
  $\nu((0,\infty))>0$ implies $\mathbb P(C_n)>0$ for every $n$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.survivalProbability_antitone`:
  $n\le m$ implies $\mathbb P(C_m)\le\mathbb P(C_n)$.
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
This is the conditional law in Caravenna--Chaumont, equation (3.3). -/
noncomputable def survivalConditionedLaw (ν : Measure ℝ) (n : ℕ) :
    Measure (ℕ → ℝ) :=
  (iidSequenceLaw ν)[|{increment | SurvivesNonnegative n increment}]

/-- Positive increments at every step form a positive-probability event
contained in survival through time `n`. -/
theorem survivalProbability_pos_of_positiveIncrement
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpositive : 0 < ν (Set.Ioi 0)) (n : ℕ) :
    0 < (iidSequenceLaw ν)
      {increment | SurvivesNonnegative n increment} := by
  have hsubset :
      {increment : ℕ → ℝ | ∀ k < n, increment k ∈ Set.Ioi 0} ⊆
      {increment | SurvivesNonnegative n increment} := by
    intro increment hinc k
    rw [AdditivePath.displacement]
    exact Finset.sum_nonneg fun i hi =>
      (hinc i (lt_of_lt_of_le (Finset.mem_range.mp hi)
        (Nat.succ_le_of_lt k.isLt))).le
  have hmass := iidSequenceLaw_measure_forall_lt ν (Set.Ioi 0)
    measurableSet_Ioi n
  calc
    0 < (ν (Set.Ioi 0)) ^ n :=
      (pos_iff_ne_zero).2 (pow_ne_zero n (ne_of_gt hpositive))
    _ = (iidSequenceLaw ν)
        {increment | ∀ k < n, increment k ∈ Set.Ioi 0} := hmass.symm
    _ ≤ (iidSequenceLaw ν)
        {increment | SurvivesNonnegative n increment} :=
      measure_mono hsubset

/-- The probability of surviving through time `n` decreases with the
horizon. This is the monotonicity used alongside the survival asymptotic
in Caravenna--Chaumont, Lemma 2.1. -/
theorem survivalProbability_antitone
    (ν : Measure ℝ) {n m : ℕ} (hnm : n ≤ m) :
    (iidSequenceLaw ν) {increment | SurvivesNonnegative m increment} ≤
      (iidSequenceLaw ν) {increment | SurvivesNonnegative n increment} :=
  measure_mono fun _ h => h.mono hnm

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
Wang Yiyang, *Asymptotic speed of the $N$-branching random walk with
infinite offspring*, Chapter 3, Lemma 3.5, Appendix A.2. -/
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

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end

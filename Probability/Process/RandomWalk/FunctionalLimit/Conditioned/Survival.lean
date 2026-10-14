/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Survival
public import Probability.Sequence.IID
public import Mathlib.Probability.ConditionalProbability

/-!
# Random-walk laws conditioned on nonnegative survival

The public objects and theorems in this file are:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.survivalConditionedLaw`:
  the i.i.d. increment law conditioned on
  $C_n=\{S_j\ge0:1\le j\le n\}$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.survivalConditionedLaw_isProbabilityMeasure`:
  $\mathbb P(C_n)>0$ makes the conditioned law a probability measure.
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

/-- Positive survival probability normalizes the conditional law. -/
theorem survivalConditionedLaw_isProbabilityMeasure
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ)
    (hpositive : (iidSequenceLaw ν)
      {increment | SurvivesNonnegative n increment} ≠ 0) :
    IsProbabilityMeasure (survivalConditionedLaw ν n) := by
  unfold survivalConditionedLaw
  exact cond_isProbabilityMeasure hpositive

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

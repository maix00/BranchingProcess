/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Survival
public import Probability.Sequence.IID

/-!
# Probabilities of finite nonnegative survival

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.survivalProbability_pos_of_positiveIncrement`:
  if $\nu((0,\infty))>0$, then
  $\mathbb P(S_j\ge0\text{ for }1\le j\le n)>0$ for every $n$.
- `ProbabilityTheory.RandomWalk.survivalProbability_antitone`:
  if $n\le m$, then $\mathbb P(C_m)\le\mathbb P(C_n)$.

These are elementary finite-path properties of the survival event used in
Francesco Caravenna and Loïc Chaumont, *Invariance principles for random
walks conditioned to stay positive*, Lemma 2.1 and equation (3.3),
DOI 10.1214/07-AIHP119.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

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

/-- Survival probability decreases with the time horizon. -/
theorem survivalProbability_antitone
    (ν : Measure ℝ) {n m : ℕ} (hnm : n ≤ m) :
    (iidSequenceLaw ν) {increment | SurvivesNonnegative m increment} ≤
      (iidSequenceLaw ν) {increment | SurvivesNonnegative n increment} :=
  measure_mono fun _ h => h.mono hnm

end ProbabilityTheory.RandomWalk

end

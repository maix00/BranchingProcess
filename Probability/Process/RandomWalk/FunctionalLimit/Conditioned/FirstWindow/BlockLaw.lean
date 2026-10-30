/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.Process.RandomWalk.FunctionalLimit.Conditioned.FirstWindow.Lemmas.PrefixEvent
import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.FirstWindow.Existence
import all Probability.Process.RandomWalk.FunctionalLimit.Conditioned.FirstWindow.Lemmas.BlockFactorization
public import Combinatorics.Sequence.Block
public import Algebra.BigOperators.PartialSum
public import Probability.Process.RandomWalk.Path.Survival.Basic
import Probability.Process.RandomWalk.Path.Survival.Probability
import Probability.Sequence.Block
public import Probability.Sequence.IID.Basic
import MeasureTheory.Function.FinPartialSum

/-!
# The law of the first surviving block

## Public declarations

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_firstWindow_block_union_eq_conditionalBlock`:
  for every measurable $A\subseteq\mathbb R^n$,
  $\mathbb P_\nu(\text{selected block}\in A)=
  \frac{\mathbb P_\nu(\text{initial block}\in A,\ S_k\ge0\ (1\le k\le n))}
  {\mathbb P_\nu(S_k\ge0\ (1\le k\le n))}$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_firstWindow_partialSums_bounded_eq_conditional`:
  for every threshold vector $x$, this identity applies to
  $A=\{y:\sum_{i=1}^k y_i\le x_k,\ 1\le k\le n\}$.

The second statement is Erwin Bolthausen's Lemma 3.1 in its displayed
finite-dimensional form, p. 482, in *On a Functional Central Limit Theorem
for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976),
480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

/-- The law of the first surviving length-$n$ increment block is the
law of the initial block conditioned to survive. This is the measurable
finite-block form of Lemma 3.1 in Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*,
pp. 482--483, DOI 10.1214/aop/1176996098. -/
theorem measure_firstWindow_block_union_eq_conditionalBlock
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpositive : 0 < ν (Set.Ioi 0))
    (n : ℕ) (event : Set (Fin n → ℝ))
    (hevent : MeasurableSet event) :
    (iidSequenceLaw ν)
      (⋃ start : ℕ,
        {increment | IsFirstSurvivingWindow n start increment} ∩
          (Combinatorics.Sequence.blockCoordinates start n) ⁻¹' event) =
      (iidSequenceLaw ν)
        ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
          (event ∩ {block | FiniteSurvivesNonnegative block})) /
      (iidSequenceLaw ν)
        ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
          {block | FiniteSurvivesNonnegative block}) := by
  let μ := iidSequenceLaw ν
  let s : ℝ≥0∞ := ∑' start : ℕ,
    μ {increment | NoEarlierSurvivingPrefix n start increment}
  let q : ℝ≥0∞ := μ
    ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
      {block | FiniteSurvivesNonnegative block})
  let p : ℝ≥0∞ := μ
    ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
      (event ∩ {block | FiniteSurvivesNonnegative block}))
  have hqpos : 0 < q := by
    have hp := survivalProbability_pos_of_positiveIncrement ν hpositive n
    have hset :
        (Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
          {block | FiniteSurvivesNonnegative block} =
        {increment | SurvivesNonnegative n increment} := by
      ext increment
      change FiniteSurvivesNonnegative
        (Combinatorics.Sequence.blockCoordinates 0 n increment) ↔
          SurvivesNonnegative n increment
      simpa only [zero_add] using
        (finiteSurvivesNonnegative_blockCoordinates_iff n 0 increment)
    simpa only [q, hset] using hp
  have hqfinite : q ≠ ∞ := measure_ne_top _ _
  have hnormal : s * q = 1 := by
    have h := measure_firstWindow_block_union_eq_tsum ν n Set.univ
      MeasurableSet.univ
    have hcover := measure_exists_firstSurvivingWindow_eq_one ν hpositive n
    have h' : μ (⋃ start : ℕ,
        {increment | IsFirstSurvivingWindow n start increment}) =
        s * q := by
      simpa only [Set.preimage_univ, Set.inter_univ, Set.univ_inter,
        s, q] using h
    rw [hcover] at h'
    exact h'.symm
  have hmain := measure_firstWindow_block_union_eq_tsum ν n event hevent
  apply (ENNReal.eq_div_iff hqpos.ne' hqfinite).2
  rw [hmain]
  change q * (s * p) = p
  calc
    q * (s * p) = (s * q) * p := by ac_rfl
    _ = p := by rw [hnormal]; simp

/-- Bolthausen's Lemma 3.1 in its displayed finite-dimensional form:
the partial sums of the first surviving length-`n` block have the law
of the original partial sums conditioned on nonnegative survival.
See Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Lemma 3.1, p. 482,
DOI 10.1214/aop/1176996098. -/
theorem measure_firstWindow_partialSums_bounded_eq_conditional
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpositive : 0 < ν (Set.Ioi 0))
    (n : ℕ) (threshold : Fin n → ℝ) :
    (iidSequenceLaw ν)
      (⋃ start : ℕ,
        {increment | IsFirstSurvivingWindow n start increment} ∩
          (Combinatorics.Sequence.blockCoordinates start n) ⁻¹'
            {block : Fin n → ℝ |
              ∀ k : Fin n, Fin.partialSum block k.succ ≤ threshold k}) =
      (iidSequenceLaw ν)
        ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
          ({block : Fin n → ℝ |
            ∀ k : Fin n, Fin.partialSum block k.succ ≤ threshold k} ∩
            {block | FiniteSurvivesNonnegative block})) /
      (iidSequenceLaw ν)
        ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
          {block | FiniteSurvivesNonnegative block}) := by
  apply measure_firstWindow_block_union_eq_conditionalBlock ν hpositive n
  rw [show {block : Fin n → ℝ |
      ∀ k : Fin n, Fin.partialSum block k.succ ≤ threshold k} =
      ⋂ k : Fin n,
        {block | Fin.partialSum block k.succ ≤ threshold k} by
      ext block
      simp]
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_le
    (Fin.measurable_partialSum k.succ) measurable_const

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end

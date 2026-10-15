/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.InclusionExclusion
public import Probability.Process.RandomWalk.Path.Survival
public import Probability.Sequence.IID

/-!
# The cyclic rotation inequality for IID random walks

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.measure_nonnegativeEndpoint_le_card_mul_survival`:
  for every $N\ge1$ and any i.i.d. real increments,
  $\mathbb P(S_N\ge0)\le N\mathbb P(S_j\ge0\text{ for }1\le j\le N)$.

The proof uses the finite-path rotation cover in Bauer--Godrèche--Luck,
*Statistics of persistent events in the binomial random walk: Will the
drunken sailor hit the sober man?*, Appendix A, immediately after (A.3)
(arXiv:cond-mat/9905252), and invariance of the finite IID product law
under a cyclic coordinate permutation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk

private theorem partialSum_prefix_eq_displacement
    (n : ℕ) (increment : ℕ → ℝ) (t : Fin (n + 1)) :
    Fin.partialSum (fun i : Fin n => increment i.val) t =
      AdditivePath.displacement t.val increment := by
  induction t using Fin.induction with
  | zero => simp [AdditivePath.displacement]
  | succ k ih =>
      rw [Fin.partialSum_succ, ih]
      simp [AdditivePath.displacement, Finset.sum_range_succ]

private theorem measurable_finitePartialSum {n : ℕ}
    (t : Fin (n + 1)) :
    Measurable (fun z : Fin n → ℝ => Fin.partialSum z t) := by
  induction t using Fin.induction with
  | zero => simp
  | succ k ih =>
      rw [show (fun z : Fin n → ℝ => Fin.partialSum z k.succ) =
        (fun z => Fin.partialSum z k.castSucc + z k) by
          funext z
          rw [Fin.partialSum_succ]]
      exact ih.add (measurable_pi_apply k)

private theorem finiteSurvivalEvent_eq_infinite
    (n : ℕ) (increment : ℕ → ℝ) :
    (∀ t : Fin (n + 1), 0 ≤ Fin.partialSum
      (fun i : Fin n => increment i.val) t) ↔
      SurvivesNonnegative n increment := by
  constructor
  · intro h k
    simpa only [partialSum_prefix_eq_displacement, Fin.val_succ] using h k.succ
  · intro h t
    induction t using Fin.induction with
    | zero => simp
    | succ k ih =>
        simpa only [partialSum_prefix_eq_displacement, Fin.val_succ] using h k

/-- The endpoint probability is at most the number of rotations times the
nonnegative-survival probability. Only the IID law is assumed. -/
theorem measure_nonnegativeEndpoint_le_card_mul_survival
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) :
    iidSequenceLaw ν
        {increment | 0 ≤ AdditivePath.displacement n increment} ≤
      n • iidSequenceLaw ν
        {increment | SurvivesNonnegative n increment} := by
  have hfinite := measure_pi_nonnegative_endpoint_le_card_mul_survival ν hn
  have hmeasEndpoint : MeasurableSet
      {z : Fin n → ℝ | 0 ≤ Fin.partialSum z (Fin.last n)} := by
    exact measurableSet_Ici.preimage (measurable_finitePartialSum (Fin.last n))
  have hmeasSurvival : MeasurableSet
      {z : Fin n → ℝ | ∀ t : Fin (n + 1), 0 ≤ Fin.partialSum z t} := by
    rw [show {z : Fin n → ℝ | ∀ t : Fin (n + 1), 0 ≤ Fin.partialSum z t} =
        ⋂ t : Fin (n + 1), {z | 0 ≤ Fin.partialSum z t} by ext z; simp]
    exact MeasurableSet.iInter fun t =>
      measurableSet_Ici.preimage (measurable_finitePartialSum t)
  have hprefix : Measurable (fun increment : ℕ → ℝ =>
      fun i : Fin n => increment i.val) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply i.val
  rw [← iidSequenceLaw_map_finPrefix ν n] at hfinite
  rw [Measure.map_apply hprefix hmeasEndpoint,
    Measure.map_apply hprefix hmeasSurvival] at hfinite
  change (iidSequenceLaw ν)
      {increment | 0 ≤ Fin.partialSum
        (fun i : Fin n => increment i.val) (Fin.last n)} ≤
    n • (iidSequenceLaw ν)
      {increment | ∀ t : Fin (n + 1),
        0 ≤ Fin.partialSum (fun i : Fin n => increment i.val) t} at hfinite
  have hendpoint :
      {increment : ℕ → ℝ |
        0 ≤ Fin.partialSum (fun i : Fin n => increment i.val) (Fin.last n)} =
      {increment | 0 ≤ AdditivePath.displacement n increment} := by
    ext increment
    simp only [partialSum_prefix_eq_displacement, Fin.val_last]
  have hsurvival :
      {increment : ℕ → ℝ | ∀ t : Fin (n + 1),
        0 ≤ Fin.partialSum (fun i : Fin n => increment i.val) t} =
      {increment | SurvivesNonnegative n increment} := by
    ext increment
    exact finiteSurvivalEvent_eq_infinite n increment
  rw [hendpoint, hsurvival] at hfinite
  exact hfinite

end ProbabilityTheory.RandomWalk

end

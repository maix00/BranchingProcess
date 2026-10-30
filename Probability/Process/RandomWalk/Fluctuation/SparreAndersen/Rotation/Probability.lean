/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.AdditivePath.Basic
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Probability.Process.RandomWalk.Path.Survival.Basic
public import Probability.Sequence.IID.Basic
import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Rotation.FiniteProduct
import MeasureTheory.Function.FinPartialSum

/-!
# The cyclic rotation inequality for IID random walks

## Public declarations

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.measure_nonnegativeEndpoint_le_card_mul_survival`:
  for every $N\ge1$ and any i.i.d. real increments,
  $\mathbb P(S_N\ge0)\le N\mathbb P(S_j\ge0\text{ for }1\le j\le N)$.

The proof uses the finite-path rotation cover in M. Bauer, C. Godrèche,
and J.-M. Luck, *Statistics of persistent events in the binomial random
walk: Will the drunken sailor hit the sober man?*, Appendix A, immediately
after equation (A.3), *Journal of Statistical Physics* 96 (1999),
963--1019, DOI 10.1023/A:1004636216365, arXiv:cond-mat/9905252, and
invariance of the finite IID product law under a cyclic coordinate
permutation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk

/-- The endpoint probability is at most the number of rotations times the
nonnegative-survival probability. Only the IID law is assumed. -/
theorem measure_nonnegativeEndpoint_le_card_mul_survival
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) :
    iidSequenceLaw ν
        {increment | 0 ≤ AdditivePath.displacement n increment} ≤
      n • iidSequenceLaw ν
        {increment | SurvivesNonnegative n increment} := by
  have hfinite := measure_pi_nonnegative_endpoint_le_card_mul_survival
    measurableSet_Ici ν hn
  have hmeasEndpoint : MeasurableSet
      {z : Fin n → ℝ | 0 ≤ Fin.partialSum z (Fin.last n)} := by
    exact measurableSet_Ici.preimage (Fin.measurable_partialSum (Fin.last n))
  have hmeasSurvival : MeasurableSet
      {z : Fin n → ℝ | ∀ t : Fin (n + 1), 0 ≤ Fin.partialSum z t} := by
    exact measurableSet_nonnegativePartialSum measurableSet_Ici
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
    simp only [AdditivePath.partialSum_eq_displacement, Fin.val_last]
  have hsurvival :
      {increment : ℕ → ℝ | ∀ t : Fin (n + 1),
        0 ≤ Fin.partialSum (fun i : Fin n => increment i.val) t} =
      {increment | SurvivesNonnegative n increment} := by
    ext increment
    exact finitePartialSum_nonnegative_iff_survivesNonnegative n increment
  rw [hendpoint, hsurvival] at hfinite
  exact hfinite

end ProbabilityTheory.RandomWalk

end

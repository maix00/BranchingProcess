/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Distributions.Moments.Signs
import Mathlib.Data.Set.Defs
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.Pi
import Algebra.BigOperators.AdditivePath.Basic
import MeasureTheory.Function.FinPartialSum
import Probability.Process.RandomWalk.Path.Survival.Basic
import Probability.Process.RandomWalk.Path.Survival.Probability
import Probability.Sequence.IID.Basic

/-!
# Internal finite-horizon estimates for the survival lower bound

## Internal proof declarations

- `finiteSurvivalProbability_eq_infinite` and
  `finiteEndpointProbability_eq_infinite` transfer finite-product probabilities
  to events of the infinite IID sequence.
- `finiteSurvivalProbability_zero` gives the empty-horizon initial value.
- `recurrence_to_convolution` rewrites the endpoint recurrence as a convolution.
- `prefix_bound_of_convolution` extracts a lower bound on survival from a
  uniform endpoint-sign lower bound.

These declarations support only
`Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Survival.FiniteVarianceLower`.
-/

open MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk

lemma finiteSurvivalProbability_eq_infinite
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.pi (fun _ : Fin n => ν)).real
      {z : Fin n → ℝ | ∀ t : Fin (n + 1), 0 ≤ Fin.partialSum z t} =
      ((iidSequenceLaw ν) {increment | SurvivesNonnegative n increment}).toReal := by
  change ((Measure.pi (fun _ : Fin n => ν))
      {z : Fin n → ℝ | ∀ t : Fin (n + 1), 0 ≤ Fin.partialSum z t}).toReal = _
  rw [← iidSequenceLaw_map_finPrefix ν n]
  rw [Measure.map_apply (measurable_pi_iff.mpr fun i => measurable_pi_apply i.val)
      (measurableSet_nonnegativePartialSum measurableSet_Ici)]
  apply congrArg ENNReal.toReal
  apply congrArg (iidSequenceLaw ν)
  ext increment
  exact finitePartialSum_nonnegative_iff_survivesNonnegative n increment

lemma finiteEndpointProbability_eq_infinite
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.pi (fun _ : Fin n => ν)).real
      {z : Fin n → ℝ | 0 ≤ Fin.partialSum z (Fin.last n)} =
      ((iidSequenceLaw ν)
        {increment | 0 ≤ AdditivePath.displacement n increment}).toReal := by
  change ((Measure.pi (fun _ : Fin n => ν))
      {z : Fin n → ℝ | 0 ≤ Fin.partialSum z (Fin.last n)}).toReal = _
  rw [← iidSequenceLaw_map_finPrefix ν n]
  have hs : MeasurableSet {z : Fin n → ℝ | 0 ≤ Fin.partialSum z (Fin.last n)} := by
    exact measurableSet_Ici.preimage (Fin.measurable_partialSum (Fin.last n))
  rw [Measure.map_apply (measurable_pi_iff.mpr fun i => measurable_pi_apply i.val) hs]
  apply congrArg ENNReal.toReal
  apply congrArg (iidSequenceLaw ν)
  ext increment
  simp only [Set.mem_preimage, Set.mem_ofPred_eq,
    AdditivePath.partialSum_eq_displacement, Fin.val_last]

lemma finiteSurvivalProbability_zero
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (Measure.pi (fun _ : Fin 0 => ν)).real
      {z : Fin 0 → ℝ | ∀ t : Fin 1, 0 ≤ Fin.partialSum z t} = 1 := by
  have hevent : {z : Fin 0 → ℝ | ∀ t : Fin 1, 0 ≤ Fin.partialSum z t} = Set.univ := by
    ext z
    simp [Fin.forall_fin_succ]
  rw [hevent]
  simp

lemma recurrence_to_convolution
    (F P : ℕ → ℝ) (hF0 : F 0 = 1)
    (hrec : ∀ n : ℕ, 0 < n →
      P n = (n : ℝ) * F n -
        ∑ r : Fin (n - 1), F (r.val + 1) * P (n - (r.val + 1)))
    {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * F n = ∑ k : Fin n, F k.val * P (n - k.val) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.sub_zero, hF0, one_mul, Fin.val_succ]
  have h := hrec (m + 1) (by omega)
  simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc] using
    (sub_eq_iff_eq_add.mp h.symm)

lemma prefix_bound_of_convolution
    (F P : ℕ → ℝ) (hFnonneg : ∀ k, 0 ≤ F k)
    (hPnonneg : ∀ j, 0 ≤ P j)
    {β : ℝ} (_hβ : 0 ≤ β) (N : ℕ) (_hN : 1 ≤ N)
    (hPβ : ∀ j, N ≤ j → β ≤ P j)
    (hconv : ∀ n : ℕ, 0 < n →
      (n : ℝ) * F n = ∑ k : Fin n, F k.val * P (n - k.val))
    (n : ℕ) (hn : N ≤ n) :
    β * ∑ k ∈ Finset.range (n - N + 1), F k ≤ (n : ℝ) * F n := by
  have hm : n - N + 1 ≤ n := by omega
  rw [hconv n (by omega : 0 < n)]
  have hfin : (∑ k : Fin n, F k.val * P (n - k.val)) =
      ∑ k ∈ Finset.range n, F k * P (n - k) :=
    Fin.sum_univ_eq_sum_range (fun i : ℕ => F i * P (n - i)) n
  rw [hfin]
  calc
    β * ∑ k ∈ Finset.range (n - N + 1), F k =
        ∑ k ∈ Finset.range (n - N + 1), β * F k := by
      rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range (n - N + 1), F k * P (n - k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k < n - N + 1 := Finset.mem_range.mp hk
      have hnk : N ≤ n - k := by omega
      exact mul_le_mul_of_nonneg_right (hPβ (n - k) hnk) (hFnonneg k) |>.trans_eq (mul_comm _ _)
    _ ≤ ∑ k ∈ Finset.range n, F k * P (n - k) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hm)
      · intro k _ _
        exact mul_nonneg (hFnonneg k) (hPnonneg (n - k))


end ProbabilityTheory.RandomWalk

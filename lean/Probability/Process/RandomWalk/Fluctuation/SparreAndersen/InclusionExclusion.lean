/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.RotationCover
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Inclusion and exclusion for cyclic survival

The public definitions and theorems in this file are:

- `ProbabilityTheory.RandomWalk.cyclicSurvivalEvent`: the event that the
  cyclic rotation at $k$ has all $n+1$ partial sums nonnegative.
- `ProbabilityTheory.RandomWalk.measurableSet_cyclicSurvivalEvent`:
  each such event is measurable in the finite product space.
- `ProbabilityTheory.RandomWalk.measureReal_nonnegative_endpoint_eq_cyclicSurvival_sum`:
  $\mathbb P(S_n\ge0)$ is the alternating sum of probabilities of nonempty
  intersections of cyclic survival events.

This is equation (A.4) in M. Bauer, C. Godrèche, and J.-M. Luck,
*Statistics of persistent events in the binomial random walk: Will the
drunken sailor hit the sober man?*, Appendix A (arXiv:cond-mat/9905252).
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

/-- The cyclic survival event $B_n^{k+1}$ in Bauer--Godrèche--Luck,
Appendix A, equation (A.3). -/
def cyclicSurvivalEvent {n : ℕ} (k : Fin n) : Set (Fin n → ℝ) :=
  {x | ∀ j : Fin (n + 1),
    0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) k j}

private theorem measurable_finitePartialSum {n : ℕ}
    (j : Fin (n + 1)) :
    Measurable (fun x : Fin n → ℝ => Fin.partialSum x j) := by
  induction j using Fin.induction with
  | zero => simp
  | succ j ih =>
    have hsum :
        (fun x : Fin n → ℝ => Fin.partialSum x j.succ) =
          fun x => Fin.partialSum x j.castSucc + x j :=
      funext fun x => Fin.partialSum_succ x j
    rw [hsum]
    exact ih.add (measurable_pi_apply j)

private theorem measurable_cyclicPartialSum {n : ℕ}
    (k : Fin n) (j : Fin (n + 1)) :
    Measurable (fun x : Fin n → ℝ =>
      Fin.cyclicPartialSum (Fin.partialSum x) k j) := by
  by_cases h : k.val + j.val ≤ n
  · convert (measurable_finitePartialSum
        (⟨k.val + j.val, Nat.lt_succ_of_le h⟩ : Fin (n + 1))).sub
        (measurable_finitePartialSum k.castSucc) using 1
    funext x
    simp [Fin.cyclicPartialSum, h, Pi.sub_apply]
  · convert ((measurable_finitePartialSum (Fin.last n)).sub
        (measurable_finitePartialSum k.castSucc)).add
        (measurable_finitePartialSum
          (⟨k.val + j.val - n, by omega⟩ : Fin (n + 1))) using 1
    funext x
    simp [Fin.cyclicPartialSum, h, Pi.sub_apply, Pi.add_apply]

/-- Every cyclic survival event is measurable. -/
theorem measurableSet_cyclicSurvivalEvent {n : ℕ} (k : Fin n) :
    MeasurableSet (cyclicSurvivalEvent k) := by
  have h : MeasurableSet (⋂ j : Fin (n + 1),
      {x : Fin n → ℝ |
        0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) k j}) := by
    exact MeasurableSet.iInter fun j =>
      measurableSet_Ici.preimage (measurable_cyclicPartialSum k j)
  simpa only [cyclicSurvivalEvent, Set.iInter_ofPred] using h

/-- Inclusion--exclusion for the union of cyclic survival events,
corresponding to Bauer--Godrèche--Luck, Appendix A, equation (A.4). -/
theorem measureReal_nonnegative_endpoint_eq_cyclicSurvival_sum
    {n : ℕ} (hn : 0 < n) (μ : Measure (Fin n → ℝ))
    [IsFiniteMeasure μ] :
    μ.real {x : Fin n → ℝ | 0 ≤ Fin.partialSum x (Fin.last n)} =
      ∑ u ∈ (Finset.univ : Finset (Fin n)).powerset with u.Nonempty,
        (-1 : ℝ) ^ (u.card + 1) *
          μ.real (⋂ k ∈ u, cyclicSurvivalEvent k) := by
  have hevent :
      {x : Fin n → ℝ | 0 ≤ Fin.partialSum x (Fin.last n)} =
        ⋃ k : Fin n, cyclicSurvivalEvent k := by
    simpa only [cyclicSurvivalEvent] using
      nonnegative_finitePartialSum_eq_iUnion_cyclic_survival hn
  rw [hevent]
  have hformula := measureReal_biUnion_eq_sum_powerset
    (μ := μ) (t := (Finset.univ : Finset (Fin n)))
    (s := cyclicSurvivalEvent)
    (fun k _ => measurableSet_cyclicSurvivalEvent k)
  simpa using hformula

end ProbabilityTheory.RandomWalk

end

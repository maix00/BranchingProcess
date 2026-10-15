/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.InclusionExclusion

/-!
# Prefix inequalities for cyclic survival blocks

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.cyclicSurvivalEvent_partialSum_le_of_start_le`:
  if the rotation at $k$ survives and $k\le t\le n$, then $S_k\le S_t$.
- `ProbabilityTheory.RandomWalk.cyclicSurvivalEvent_partialSum_le_of_before_start`:
  if the rotation at $k$ survives and $0\le t<k$, then
  $S_k\le S_n+S_t$.
- `ProbabilityTheory.RandomWalk.mem_cyclicSurvivalEvent_iff_partialSum`:
  the endpoint condition $S_n\ge0$ and these two families of prefix
  inequalities characterize $B_n^{k+1}$.

These are the two kinds of inequalities in the event $B_n^{k+1}$ of
M. Bauer, C. Godrèche, and J.-M. Luck, *Statistics of persistent events
in the binomial random walk: Will the drunken sailor hit the sober man?*,
Appendix A, equation (A.3) (arXiv:cond-mat/9905252). They are the
pointwise ingredients of the block decomposition in equation (A.5).
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- A surviving rotation has nonnegative partial sums from its start
up to every later time before the end of the original vector. -/
theorem cyclicSurvivalEvent_partialSum_le_of_start_le
    {n : ℕ} (x : Fin n → ℝ) (k : Fin n) (t : Fin (n + 1))
    (hkt : k.val ≤ t.val) (hx : x ∈ cyclicSurvivalEvent k) :
    Fin.partialSum x k.castSucc ≤ Fin.partialSum x t := by
  let j : Fin (n + 1) := ⟨t.val - k.val, by omega⟩
  have hsum : k.val + j.val ≤ n := by dsimp [j]; omega
  have hindex :
      (⟨k.val + j.val, Nat.lt_succ_of_le hsum⟩ : Fin (n + 1)) = t := by
    apply Fin.ext
    dsimp [j]
    omega
  have hj := hx j
  change 0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) k j at hj
  simp only [Fin.cyclicPartialSum, dite_eq_left hsum, hindex] at hj
  linarith

/-- A surviving rotation has nonnegative wrapped partial sums after
reaching the end of the original vector. -/
theorem cyclicSurvivalEvent_partialSum_le_of_before_start
    {n : ℕ} (x : Fin n → ℝ) (k : Fin n) (t : Fin (n + 1))
    (htk : t.val < k.val) (hx : x ∈ cyclicSurvivalEvent k) :
    Fin.partialSum x k.castSucc ≤
      Fin.partialSum x (Fin.last n) + Fin.partialSum x t := by
  by_cases htzero : t.val = 0
  · have ht : t = 0 := Fin.ext htzero
    subst t
    have hlast := cyclicSurvivalEvent_partialSum_le_of_start_le
      x k (Fin.last n) (by simp [Fin.val_last, Nat.le_of_lt k.isLt]) hx
    simpa using hlast
  · let j : Fin (n + 1) := ⟨n - k.val + t.val, by omega⟩
    have hwrap : ¬ k.val + j.val ≤ n := by dsimp [j]; omega
    have hindex :
        (⟨k.val + j.val - n, by omega⟩ : Fin (n + 1)) = t := by
      apply Fin.ext
      dsimp [j]
      omega
    have hj := hx j
    change 0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) k j at hj
    simp only [Fin.cyclicPartialSum, dite_eq_right hwrap, hindex] at hj
    linarith

/-- The explicit two-part description of the cyclic event $B_n^{k+1}$
in Bauer--Godrèche--Luck, Appendix A, equation (A.3). -/
theorem mem_cyclicSurvivalEvent_iff_partialSum
    {n : ℕ} (x : Fin n → ℝ) (k : Fin n) :
    x ∈ cyclicSurvivalEvent k ↔
      0 ≤ Fin.partialSum x (Fin.last n) ∧
      (∀ t : Fin (n + 1), k.val ≤ t.val →
        Fin.partialSum x k.castSucc ≤ Fin.partialSum x t) ∧
      (∀ t : Fin (n + 1), t.val < k.val →
        Fin.partialSum x k.castSucc ≤
          Fin.partialSum x (Fin.last n) + Fin.partialSum x t) := by
  constructor
  · intro hx
    have hlast := hx (Fin.last n)
    change 0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) k (Fin.last n) at hlast
    rw [Fin.cyclicPartialSum_last_eq_of_zero
      (Fin.partialSum x) (Fin.partialSum_zero x) k] at hlast
    exact ⟨hlast, fun t hkt =>
      cyclicSurvivalEvent_partialSum_le_of_start_le x k t hkt hx,
      fun t htk =>
        cyclicSurvivalEvent_partialSum_le_of_before_start x k t htk hx⟩
  · rintro ⟨hlast, hfirst, hsecond⟩
    intro j
    by_cases hjlast : j = Fin.last n
    · subst j
      simpa [Fin.cyclicPartialSum_last_eq_of_zero
        (Fin.partialSum x) (Fin.partialSum_zero x) k] using hlast
    by_cases hsum : k.val + j.val ≤ n
    · let t : Fin (n + 1) :=
        ⟨k.val + j.val, Nat.lt_succ_of_le hsum⟩
      have hkt : k.val ≤ t.val := by dsimp [t]; omega
      have h := hfirst t hkt
      have hnonneg :
          0 ≤ Fin.partialSum x t - Fin.partialSum x k.castSucc := by
        linarith
      simpa only [cyclicSurvivalEvent, Fin.cyclicPartialSum,
        dite_eq_left hsum] using hnonneg
    · let t : Fin (n + 1) :=
        ⟨k.val + j.val - n, by omega⟩
      have htk : t.val < k.val := by
        dsimp [t]
        have hj : j.val < n := by
          have hjle : j.val ≤ n := Nat.le_of_lt_succ j.isLt
          have hjne : j.val ≠ n := by
            intro heq
            exact hjlast (Fin.ext (by simpa [Fin.val_last] using heq))
          omega
        omega
      have h := hsecond t htk
      have hnonneg :
          0 ≤ Fin.partialSum x (Fin.last n) -
            Fin.partialSum x k.castSucc + Fin.partialSum x t := by
        linarith
      simpa only [Fin.cyclicPartialSum, dite_eq_right hsum] using hnonneg

end ProbabilityTheory.RandomWalk

end

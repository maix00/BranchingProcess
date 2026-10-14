/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Survival

/-!
# Strict record local time of a random walk

The public definitions and theorems in this file are:

- ProbabilityTheory.RandomWalk.IsStrictAscendingRecord:
  $S_n>\max_{0\le j<n}S_j$ for $n\ge1$.
- ProbabilityTheory.RandomWalk.strictAscendingLocalTime:
  $\ell_n=\#\{1\le j\le n:S_j>\max_{0\le i<j}S_i\}$.
- ProbabilityTheory.RandomWalk.strictAscendingLocalTime_zero:
  $\ell_0=0$.
- ProbabilityTheory.RandomWalk.strictAscendingLocalTime_succ:
  $\ell_{n+1}=\ell_n+1_{\{S_{n+1}>\max_{i\le n}S_i\}}$.
- ProbabilityTheory.RandomWalk.strictAscendingLocalTime_mono:
  $n\le m$ implies $\ell_n\le\ell_m$.
- ProbabilityTheory.RandomWalk.measurableSet_isStrictAscendingRecord:
  the strict record event at every finite time is measurable.
- ProbabilityTheory.RandomWalk.strictAscendingLocalTime_measurable:
  the finite record count is measurable.

The definition is equation (2.2) of Loïc Chaumont and R. A. Doney,
*Invariance principles for local times at the maximum of random walks and
Lévy processes*, Ann. Probab. 38(4) (2010), 1368–1389,
DOI 10.1214/09-AOP512.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

attribute [local instance] Classical.propDecidable

/-- A positive time at which the walk strictly exceeds every earlier
position; Chaumont--Doney, equation (2.2). -/
def IsStrictAscendingRecord (increment : ℕ → ℝ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ j < n,
    AdditivePath.displacement j increment <
      AdditivePath.displacement n increment

/-- Number of strict ascending records through time n, the discrete
local time at the maximum in Chaumont--Doney, equation (2.2). -/
noncomputable def strictAscendingLocalTime (increment : ℕ → ℝ) (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (IsStrictAscendingRecord increment)).card

/-- There are no positive-time records at time zero. -/
theorem strictAscendingLocalTime_zero (increment : ℕ → ℝ) :
    strictAscendingLocalTime increment 0 = 0 := by
  simp [strictAscendingLocalTime]

/-- The record count gains one precisely at a strict ascending record. -/
theorem strictAscendingLocalTime_succ (increment : ℕ → ℝ) (n : ℕ) :
    strictAscendingLocalTime increment (n + 1) =
      strictAscendingLocalTime increment n +
        if IsStrictAscendingRecord increment (n + 1) then 1 else 0 := by
  have hinterval :
      Finset.Icc 1 (n + 1) =
        insert (n + 1) (Finset.Icc 1 n) :=
    (Finset.insert_Icc_right_eq_Icc_succ (by omega : 1 ≤ n + 1)).symm
  have hnot :
      n + 1 ∉
        (Finset.Icc 1 n).filter (IsStrictAscendingRecord increment) := by
    simp [Finset.mem_filter, Finset.mem_Icc]
  simp only [strictAscendingLocalTime, hinterval, Finset.filter_insert]
  split_ifs <;> simp [Finset.card_insert_of_notMem hnot]

/-- The strict record count is nondecreasing in the time horizon. -/
theorem strictAscendingLocalTime_mono
    (increment : ℕ → ℝ) {n m : ℕ} (hnm : n ≤ m) :
    strictAscendingLocalTime increment n ≤
      strictAscendingLocalTime increment m := by
  exact Finset.card_le_card
    (Finset.filter_subset_filter (IsStrictAscendingRecord increment)
      (Finset.Icc_subset_Icc_right hnm))

/-- The strict ascending record event is measurable in the increment
sequence. -/
theorem measurableSet_isStrictAscendingRecord (n : ℕ) :
    MeasurableSet
      {increment : ℕ → ℝ | IsStrictAscendingRecord increment n} := by
  by_cases hn : 0 < n
  · have hset :
        {increment : ℕ → ℝ | IsStrictAscendingRecord increment n} =
          ⋂ j : Fin n,
            {increment |
              AdditivePath.displacement j increment <
                AdditivePath.displacement n increment} := by
      ext increment
      simp [IsStrictAscendingRecord, hn, Fin.forall_iff]
    rw [hset]
    exact MeasurableSet.iInter fun j =>
      measurableSet_lt
        (displacement_measurable j)
        (displacement_measurable n)
  · have hempty :
        {increment : ℕ → ℝ | IsStrictAscendingRecord increment n} = ∅ := by
      ext increment
      simp [IsStrictAscendingRecord, hn]
    rw [hempty]
    exact MeasurableSet.empty

/-- The finite discrete local time at the maximum is measurable. -/
theorem strictAscendingLocalTime_measurable (n : ℕ) :
    Measurable (fun increment : ℕ → ℝ =>
      strictAscendingLocalTime increment n) := by
  classical
  have hsum : Measurable (fun increment : ℕ → ℝ =>
      ∑ j ∈ Finset.Icc 1 n,
        if IsStrictAscendingRecord increment j then (1 : ℕ) else 0) :=
    Finset.measurable_sum _ fun j _ =>
      measurable_const.ite (measurableSet_isStrictAscendingRecord j)
        measurable_const
  convert hsum using 1
  ext increment
  exact (Finset.sum_boole (IsStrictAscendingRecord increment)
    (Finset.Icc 1 n)).symm

end ProbabilityTheory.RandomWalk

end

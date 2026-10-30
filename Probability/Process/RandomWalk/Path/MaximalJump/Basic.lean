/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite maxima of random-walk increments

## Public declarations

* `ProbabilityTheory.RandomWalk.maxAbsUpTo n ξ` is
  $\max_{0\leq k\leq n}|\xi_k|$; the accompanying lemmas bound each included
  increment by this maximum, show it is nonnegative, and prove measurability
  on the product sequence space.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- Largest absolute increment among indices `0, ..., n`. -/
def maxAbsUpTo (n : ℕ) (increment : ℕ → ℝ) : ℝ :=
  (Finset.range (n + 1)).sup' (by simp) fun k ↦ |increment k|

theorem abs_increment_le_maxAbsUpTo {n k : ℕ} (increment : ℕ → ℝ)
    (hk : k ≤ n) :
    |increment k| ≤ maxAbsUpTo n increment := by
  exact Finset.le_sup' (fun i ↦ |increment i|)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk))

theorem maxAbsUpTo_nonneg (n : ℕ) (increment : ℕ → ℝ) :
    0 ≤ maxAbsUpTo n increment := by
  exact (abs_nonneg (increment 0)).trans
    (abs_increment_le_maxAbsUpTo increment (Nat.zero_le n))

theorem measurable_maxAbsUpTo (n : ℕ) :
    Measurable (maxAbsUpTo n) := by
  unfold maxAbsUpTo
  exact Finset.measurable_range_sup'' fun k _ ↦
    Measurable.abs (measurable_pi_apply k :
      Measurable (fun increment : ℕ → ℝ ↦ increment k))

end ProbabilityTheory.RandomWalk

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Basic
public import Probability.Process.RandomWalk.Rademacher.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Integer coordinates and range events of Rademacher paths

## Public declarations

The range estimate covers a Rademacher path by translated lattice intervals.
This file records the integer-lattice and linear-growth facts needed for
that finite cover.  Its public declarations are:

* `rademacherIntIncrement` assigns $1$ to `true` and $-1$ to `false`;
  `rademacherOfBool_eq_intCast` identifies its real cast with the project's
  Rademacher increment.
* `rademacherPartialSum` is the displacement of the first $n$ increments;
  `rademacherPartialSum_eq_intCast` gives
  $S_n=\sum_{k<n}\eta(b_k)\in\mathbb Z$,
  while `rademacherPartialSum_zero` and `rademacherPartialSum_succ` give
  $S_0=0$ and $S_{n+1}=S_n+\eta(b_n)$.
* `abs_rademacherRealPartialSum_le` proves $|S_n|\le n$.
* `RademacherOscillationBounded` is the event predicate
  $|S_i-S_j|\le w$ for all $0\le i,j\le n$.

The finite-family translation argument used to cover this event is stated
independently of the Rademacher model in `Order.Bounds`.
-/

open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval

/-- Integer version of a Boolean Rademacher increment. -/
def rademacherIntIncrement (branch : Bool) : ℤ :=
  if branch then 1 else -1

@[simp]
theorem rademacherOfBool_eq_intCast (branch : Bool) :
    ProbabilityTheory.rademacherOfBool branch =
      (rademacherIntIncrement branch : ℝ) := by
  cases branch <;> simp [rademacherIntIncrement,
    ProbabilityTheory.rademacherOfBool]

/-- The canonical partial sum of the project's Rademacher increment path. -/
abbrev rademacherPartialSum (n : ℕ) (branch : ℕ → Bool) : ℝ :=
  AdditivePath.displacement n
    (ProbabilityTheory.RandomWalk.rademacherIncrementPath branch)

/-- The real partial sum is the cast of an integer lattice sum. -/
theorem rademacherPartialSum_eq_intCast
    (n : ℕ) (branch : ℕ → Bool) :
    rademacherPartialSum n branch =
      (∑ k ∈ Finset.range n, rademacherIntIncrement (branch k) : ℤ) := by
  simp only [rademacherPartialSum, AdditivePath.displacement,
    ProbabilityTheory.RandomWalk.rademacherIncrementPath]
  simp only [rademacherOfBool_eq_intCast]
  norm_cast

@[simp]
theorem rademacherPartialSum_zero (branch : ℕ → Bool) :
    rademacherPartialSum 0 branch = 0 := by
  simp [rademacherPartialSum]

theorem rademacherPartialSum_succ (n : ℕ) (branch : ℕ → Bool) :
    rademacherPartialSum (n + 1) branch =
      rademacherPartialSum n branch +
        ProbabilityTheory.rademacherOfBool (branch n) := by
  rw [rademacherPartialSum, AdditivePath.displacement_succ]
  rfl

/-- A length-`n` Rademacher partial sum lies in the lattice interval
`[-n,n]`. -/
theorem abs_rademacherRealPartialSum_le
    (n : ℕ) (branch : ℕ → Bool) :
    |rademacherPartialSum n branch| ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [rademacherPartialSum_succ]
      have hstep :
          |ProbabilityTheory.rademacherOfBool (branch n)| = 1 := by
        cases branch n <;> simp [ProbabilityTheory.rademacherOfBool]
      calc
        |rademacherPartialSum n branch +
            ProbabilityTheory.rademacherOfBool (branch n)| ≤
            |rademacherPartialSum n branch| +
              |ProbabilityTheory.rademacherOfBool (branch n)| := abs_add_le _ _
        _ ≤ (n : ℝ) + 1 := add_le_add ih hstep.le
        _ = (↑(n + 1) : ℝ) := by norm_cast

/-- Finite-time range event for a Boolean Rademacher path. -/
def RademacherOscillationBounded (n : ℕ) (width : ℝ)
    (branch : ℕ → Bool) : Prop :=
  ∀ i j : Fin (n + 1),
    |rademacherPartialSum (i : ℕ) branch -
      rademacherPartialSum (j : ℕ) branch| ≤ width

end ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval

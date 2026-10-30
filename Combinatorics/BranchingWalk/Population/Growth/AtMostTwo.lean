/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Monotone.Basic

public section

/-!
# Deterministic size bounds for an immortal one-or-two-child process

## Public declarations

- `Combinatorics.Branching.Population.Growth.one_or_two_size_bounds`: if
  \(p_0=1\), \(e_n\le p_n\), and \(p_{n+1}=p_n+e_n\), then
  \(1\le p_n\le 2^n\) for every \(n\).
- `Combinatorics.Branching.Population.Growth.one_or_two_size_monotone`: the same
  recurrence with \(e_n\ge0\) makes \((p_n)\) monotone.

Every parent keeps a first child; a second child may or may not be survive.
The process is not assumed to bifurcate at every generation.
-/

namespace Combinatorics.Branching.Population.Growth


/-- The number of additional children in generation `n` cannot exceed the
number of parents. -/
theorem one_or_two_size_bounds (population extras : ℕ → ℕ)
    (hzero : population 0 = 1)
    (hextras : ∀ n, extras n ≤ population n)
    (hrec : ∀ n, population (n + 1) = population n + extras n) :
    ∀ n, 1 ≤ population n ∧ population n ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
      constructor
      · rw [hrec n]
        omega
      · rw [hrec n, Nat.pow_succ]
        have he := hextras n
        omega

/-- The immortal first-child line makes the population nondecreasing. -/
theorem one_or_two_size_monotone (population extras : ℕ → ℕ)
    (hrec : ∀ n, population (n + 1) = population n + extras n) :
    Monotone population := by
  apply monotone_nat_of_le_succ
  intro n
  rw [hrec n]
  omega

end Combinatorics.Branching.Population.Growth

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Algebra.Order.Monoid.Defs

/-!
# Multiplicative lower recurrences

An initial lower bound and a one-step multiplicative recurrence give a power
lower bound at every finite horizon:

\[
1\le u_0,\qquad
cu_n\le u_{n+1}\quad(0\le n<N)
\quad\Longrightarrow\quad
c^N\le u_N.
\]

## Public declarations

- `IsOrderedMonoid.pow_le_of_mul_le_succ` states that if `1 ≤ u 0` and
  `c * u n ≤ u (n + 1)` for `n < N`, then `c ^ N ≤ u N` for every sequence
  in an ordered commutative monoid.
-/

@[expose] public section

namespace IsOrderedMonoid

/-- A one-step multiplicative lower bound iterates to the corresponding
power lower bound in an ordered commutative monoid. -/
theorem pow_le_of_mul_le_succ {M : Type*} [CommMonoid M] [Preorder M]
    [IsOrderedMonoid M] (u : ℕ → M) (N : ℕ) (c : M)
    (hzero : 1 ≤ u 0)
    (hstep : ∀ n < N, c * u n ≤ u (n + 1)) :
    c ^ N ≤ u N := by
  have hiter : ∀ m ≤ N, c ^ m ≤ u m := by
    intro m
    induction m with
    | zero =>
        intro _
        simpa using hzero
    | succ m ih =>
        intro hm
        have hmlt : m < N := by omega
        calc
          c ^ (m + 1) = c ^ m * c := by rw [pow_succ]
          _ ≤ u m * c := IsOrderedMonoid.mul_le_mul_left _ _ (ih (by omega)) c
          _ = c * u m := mul_comm _ _
          _ ≤ u (m + 1) := hstep m hmlt
  exact hiter N le_rfl

end IsOrderedMonoid

end

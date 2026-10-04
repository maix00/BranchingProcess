/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.AdditivePath
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Deterministic bounds for partial sums

Coordinatewise bounds on a finite increment prefix give the corresponding
bounds on every partial sum.  This file contains no probability assumptions;
IID cylinder probabilities and killed-kernel applications belong to the
probability layer.
-/

open scoped BigOperators

@[expose] public section

namespace AdditivePath

variable {E : Type*} [AddCommMonoid E] [Preorder E] [AddLeftMono E]

/-- An upper bound for every increment in the first `n` coordinates gives
the expected upper bound for their partial sum. -/
theorem displacement_le_nsmul_of_forall_lt
    {increment : ℕ → E} {upper : E} {n : ℕ}
    (h : ∀ k < n, increment k ≤ upper) :
    displacement n increment ≤ n • upper := by
  unfold displacement
  simpa using Finset.sum_le_card_nsmul (Finset.range n) increment upper
    (fun k hk => h k (Finset.mem_range.mp hk))

/-- A lower bound for every increment in the first `n` coordinates gives
the expected lower bound for their partial sum. -/
theorem nsmul_le_displacement_of_forall_lt
    {increment : ℕ → E} {lower : E} {n : ℕ}
    (h : ∀ k < n, lower ≤ increment k) :
    n • lower ≤ displacement n increment := by
  unfold displacement
  simpa using Finset.card_nsmul_le_sum (Finset.range n) increment lower
    (fun k hk => h k (Finset.mem_range.mp hk))

/-- Coordinatewise interval membership bounds the partial sum between the
corresponding scalar multiples of the endpoints. -/
theorem displacement_mem_Icc_nsmul_of_forall_lt
    {increment : ℕ → E} {lower upper : E} {n : ℕ}
    (h : ∀ k < n, increment k ∈ Set.Icc lower upper) :
    displacement n increment ∈ Set.Icc (n • lower) (n • upper) :=
  ⟨nsmul_le_displacement_of_forall_lt fun k hk => (h k hk).1,
    displacement_le_nsmul_of_forall_lt fun k hk => (h k hk).2⟩

/-- The same coordinatewise bounds control every partial sum up to a fixed
horizon. -/
theorem displacement_mem_Icc_nsmul_of_forall_lt_of_le
    {increment : ℕ → E} {lower upper : E} {n : ℕ}
    (h : ∀ k < n, increment k ∈ Set.Icc lower upper)
    {k : ℕ} (hk : k ≤ n) :
    displacement k increment ∈ Set.Icc (k • lower) (k • upper) := by
  apply displacement_mem_Icc_nsmul_of_forall_lt
  intro j hj
  exact h j (hj.trans_le hk)

end AdditivePath

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.Defs

/-!
# Finite partial-sum identities

This module supplements Mathlib's `Fin.partialSum` with elementary identities
that are useful when converting between increments and positions.
-/

open scoped BigOperators

@[expose] public section

namespace Fin

variable {G : Type*} [AddCommGroup G] {n : ℕ}

/-- Partial sums of consecutive differences recover the endpoint displacement. -/
theorem partialSum_differences (f : Fin (n + 1) → G) (i : Fin (n + 1)) :
    partialSum (fun j : Fin n => f j.succ - f j.castSucc) i = f i - f 0 := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [partialSum_succ, ih]
    simp only [sub_eq_add_neg]
    calc
      f i.castSucc + -f 0 + (f i.succ + -f i.castSucc) =
          (f i.castSucc + -f i.castSucc) + (f i.succ + -f 0) := by ac_rfl
      _ = f i.succ + -f 0 := by simp

end Fin

namespace Fin

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ}

/-- Scalar multiplication commutes with finite partial summation. -/
theorem partialSum_smul (a : R) (f : Fin n → M) (i : Fin (n + 1)) :
    partialSum (fun j => a • f j) i = a • partialSum f i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [partialSum_succ, ih, partialSum_succ, smul_add]

end Fin

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.AdditivePath
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Blocks of additive paths

This file provides finite coordinate and consecutive-sum operations for an
increment sequence.
-/

open scoped BigOperators

@[expose] public section

namespace AdditivePath

/-- The finite vector of consecutive increments starting at `start`. -/
def blockCoordinates {E : Type*} (start length : ℕ)
    (increment : ℕ → E) : Fin length → E :=
  fun k => increment (start + k)

variable {E : Type*} [AddCommMonoid E]

/-- Sum of `length` consecutive increments starting at `start`. -/
def blockSum (start length : ℕ) (increment : ℕ → E) : E :=
  ∑ k ∈ Finset.Ico start (start + length), increment k

@[simp] theorem blockSum_zero (start : ℕ) (increment : ℕ → E) :
    blockSum start 0 increment = 0 := by
  simp [blockSum]

@[simp] theorem blockSum_zero_start (length : ℕ) (increment : ℕ → E) :
    blockSum 0 length increment = displacement length increment := by
  simp [blockSum, displacement]

/-- A block sum is the displacement of the increment sequence after dropping
its first `start` coordinates. -/
theorem blockSum_eq_displacement_natAdd (start length : ℕ)
    (increment : ℕ → E) :
    blockSum start length increment =
      displacement length (fun k => increment (start + k)) := by
  simp only [blockSum, displacement, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel_left]

/-- Consecutive blocks concatenate. -/
theorem blockSum_add (start m n : ℕ) (increment : ℕ → E) :
    blockSum start (m + n) increment =
      blockSum start m increment + blockSum (start + m) n increment := by
  rw [blockSum_eq_displacement_natAdd start (m + n),
    blockSum_eq_displacement_natAdd start m,
    blockSum_eq_displacement_natAdd (start + m) n,
    displacement_add]
  congr 1
  apply congrArg (fun f : ℕ → E => displacement n f)
  funext k
  congr 1
  omega

/-- The displacement through a block is the prefix displacement plus its
block sum. -/
theorem displacement_add_eq_add_blockSum (start length : ℕ)
    (increment : ℕ → E) :
    displacement (start + length) increment =
      displacement start increment + blockSum start length increment := by
  rw [displacement_add, blockSum_eq_displacement_natAdd]

section AddCommGroup

variable {G : Type*} [AddCommGroup G]

/-- Subtracting a constant from each increment subtracts its repeated sum from
the block. -/
theorem blockSum_sub_const (start length : ℕ) (increment : ℕ → G) (c : G) :
    blockSum start length (fun k => increment k - c) =
      blockSum start length increment - length • c := by
  simp [blockSum, Finset.sum_sub_distrib]

end AddCommGroup

end AdditivePath

end

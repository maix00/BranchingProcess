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


variable {E : Type*} [AddCommMonoid E]

/-- Sum of `length` consecutive increments starting at `start`. -/
def blockSum (start length : ℕ) (increment : ℕ → E) : E :=
  ∑ k ∈ Finset.Ico start (start + length), increment k

/-- Start index of the `j`-th block in a sequence of possibly unequal block
lengths. -/
def blockStart (length : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, length i

@[simp] theorem blockStart_zero (length : ℕ → ℕ) : blockStart length 0 = 0 := by
  simp [blockStart]

@[simp] theorem blockStart_succ (length : ℕ → ℕ) (j : ℕ) :
    blockStart length (j + 1) = blockStart length j + length j := by
  simp [blockStart, Finset.sum_range_succ]

theorem blockStart_const (length blocks : ℕ) :
    blockStart (fun _ => length) blocks = blocks * length := by
  induction blocks with
  | zero => simp [blockStart]
  | succ blocks ih =>
      rw [blockStart_succ, ih]
      simp [Nat.succ_mul, Nat.add_comm]

theorem blockStart_mono (length : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) :
    blockStart length i ≤ blockStart length j := by
  induction j with
  | zero => simp_all [blockStart]
  | succ j ih =>
      rw [blockStart_succ]
      by_cases h : i ≤ j
      · exact (ih h).trans (Nat.le_add_right _ _)
      · have hi : i = j + 1 := by omega
        subst i
        exact le_of_eq (blockStart_succ length j)

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

/-- A partial sum of a finite consecutive block is the corresponding
displacement of the underlying increment sequence. -/
theorem partialSum_block_eq_displacement (start length : ℕ)
    (increment : ℕ → E) (i : Fin (length + 1)) :
    Fin.partialSum (fun k : Fin length => increment (start + k)) i =
      displacement i.val (fun k => increment (start + k)) := by
  induction i using Fin.induction with
  | zero => simp [displacement, Fin.partialSum]
  | succ j hj =>
      rw [Fin.partialSum_succ, hj]
      simp [displacement_succ]

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

/-- A finite sequence of variable length blocks reconstructs the additive
path displacement at its final endpoint. -/
theorem displacement_blockStart_eq_sum_blockSum (length : ℕ → ℕ)
    (blocks : ℕ) (increment : ℕ → E) :
    displacement (blockStart length blocks) increment =
      ∑ j ∈ Finset.range blocks,
        blockSum (blockStart length j) (length j) increment := by
  induction blocks with
  | zero => simp [blockStart]
  | succ blocks ih =>
      rw [blockStart_succ, displacement_add_eq_add_blockSum, ih,
        Finset.sum_range_succ]

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

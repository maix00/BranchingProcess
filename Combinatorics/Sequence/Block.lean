/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite blocks of sequences

The public declarations in `Combinatorics.Sequence` are:

- `blockCoordinates`: the block $k\mapsto f(s+k)$, for $k<\ell$.
- `paddedBlockCoordinates`: the sequence equal to $f(s+k)$ when $k<\ell$
  and to a chosen default otherwise.
- `paddedBlockCoordinates_of_lt` and `paddedBlockCoordinates_of_not_lt`:
  $\operatorname{paddedBlock}(s,\ell,d,f)(k)=f(s+k)$ for $k<\ell$, and
  equals $d$ when $\ell\le k$.
- `blockStart`: the starting index $b_j=\sum_{i<j}\ell_i$ of the $j$-th
  consecutive block in a variable-length partition.
- `blockStart_zero` and `blockStart_succ`:
  $b_0=0$ and $b_{j+1}=b_j+\ell_j$.
- `blockStart_const` and `blockStart_mono`:
  $b_j=j\ell$ for constant block length $\ell$, and $i\le j$ implies
  $b_i\le b_j$ for arbitrary nonnegative block lengths.

Extract a finite consecutive block from an arbitrary sequence. This operation
is independent of any algebraic, probabilistic, or process structure on the
sequence values.
-/

@[expose] public section

namespace Combinatorics.Sequence

/-- Starting index of the `j`-th block in a sequence of possibly unequal
lengths. -/
def blockStart (length : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, length i

@[simp] theorem blockStart_zero (length : ℕ → ℕ) : blockStart length 0 = 0 := by
  simp [blockStart]

@[simp] theorem blockStart_succ (length : ℕ → ℕ) (j : ℕ) :
    blockStart length (j + 1) = blockStart length j + length j := by
  simp [blockStart, Finset.sum_range_succ]

/-- The start index of equal-length blocks is the block number times the
common length. -/
theorem blockStart_const (length blocks : ℕ) :
    blockStart (fun _ => length) blocks = blocks * length := by
  induction blocks with
  | zero => simp [blockStart]
  | succ blocks ih =>
      rw [blockStart_succ, ih]
      simp [Nat.succ_mul, Nat.add_comm]

/-- Cumulative block starts are monotone, since block lengths are
nonnegative. -/
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

/-- The finite block of length `length` starting at `start`. -/
def blockCoordinates {E : Type*} (start length : ℕ)
    (sequence : ℕ → E) : Fin length → E :=
  fun k => sequence (start + k)

/-- Extend a finite consecutive block to a sequence using a fixed default
outside the block. -/
def paddedBlockCoordinates {E : Type*} (start length : ℕ) (default : E)
    (sequence : ℕ → E) : ℕ → E :=
  fun k => if k < length then sequence (start + k) else default

@[simp] theorem paddedBlockCoordinates_of_lt {E : Type*}
    (start length : ℕ) (default : E) (sequence : ℕ → E) {k : ℕ}
    (hk : k < length) :
    paddedBlockCoordinates start length default sequence k = sequence (start + k) := by
  simp [paddedBlockCoordinates, hk]

@[simp] theorem paddedBlockCoordinates_of_not_lt {E : Type*}
    (start length : ℕ) (default : E) (sequence : ℕ → E) {k : ℕ}
    (hk : ¬ k < length) :
    paddedBlockCoordinates start length default sequence k = default := by
  simp [paddedBlockCoordinates, hk]

end Combinatorics.Sequence

end

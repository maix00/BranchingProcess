/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Diagonal and off-diagonal partitions of an ENNReal pair sum

## Public declarations

- `ENNReal.tsum_prod_eq_tsum_diagonal_add_offDiagonal` partitions a countable
  ENNReal sum over ordered pairs into its diagonal and off-diagonal parts:
  $\sum_{(i,j)\in I\times I} f(i,j)
    =\sum_{i\in I}f(i,i)+\sum_{i\in I}\sum_{j\in I,\,j\ne i}f(i,j)$.
  The result assumes only countability of the index type and decidable
  equality; the pair weight need not factor as a product.
-/

@[expose] public section

open scoped ENNReal

namespace ENNReal

/-- Decompose an ENNReal sum over ordered pairs into the diagonal and the
off-diagonal pairs. -/
theorem tsum_prod_eq_tsum_diagonal_add_offDiagonal
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (f : ι × ι → ℝ≥0∞) :
    (∑' p : ι × ι, f p) =
      (∑' i, f (i, i)) +
        ∑' i, ∑' j, if i ≠ j then f (i, j) else 0 := by
  classical
  have hsplit (i j : ι) :
      f (i, j) =
        (if i = j then f (i, j) else 0) +
          (if i ≠ j then f (i, j) else 0) := by
    by_cases h : i = j <;> simp [h]
  have hdiag (i : ι) :
      (∑' j, if i = j then f (i, j) else 0) = f (i, i) := by
    rw [tsum_eq_single i]
    · simp
    · intro j hj
      simp [Ne.symm hj]
  calc
    (∑' p : ι × ι, f p) = ∑' i, ∑' j, f (i, j) :=
      ENNReal.tsum_prod (f := fun i j => f (i, j))
    _ = ∑' i,
        ((∑' j, if i = j then f (i, j) else 0) +
          ∑' j, if i ≠ j then f (i, j) else 0) := by
      apply tsum_congr
      intro i
      rw [← ENNReal.tsum_add]
      apply tsum_congr
      intro j
      exact hsplit i j
    _ = (∑' i, ∑' j, if i = j then f (i, j) else 0) +
        ∑' i, ∑' j, if i ≠ j then f (i, j) else 0 :=
      ENNReal.tsum_add
    _ = (∑' i, f (i, i)) +
        ∑' i, ∑' j, if i ≠ j then f (i, j) else 0 := by
      congr 1
      apply tsum_congr
      intro i
      exact hdiag i

end ENNReal

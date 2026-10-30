/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.LinearAlgebra.Matrix.Stochastic

@[expose] public section

/-!
# Row-substochastic matrices

## Public declarations

- `Matrix.IsRowSubstochastic M` states
  $(\forall i,j,\ 0\le M_{ij})\land(\forall i,\ \sum_j M_{ij}\le1)$
  for a finite index type and a partially ordered semiring.
- `Matrix.IsRowSubstochastic.nonneg` and
  `Matrix.IsRowSubstochastic.rowSum_le_one` project the entrywise and row-sum
  bounds.
- `Matrix.IsRowSubstochastic.of_mem_rowStochastic` proves that every matrix
  with row sums equal to one in Mathlib's `Matrix.rowStochastic` set is
  row-substochastic.

This extends Mathlib's row-stochastic predicate, where each row sum equals
one, to matrices whose rows may have total mass below one.
-/

namespace Matrix

variable {ι R : Type*} [Fintype ι] [Semiring R] [PartialOrder R]

/-- A matrix is row-substochastic when its entries are nonnegative and each
row has sum at most one. -/
def IsRowSubstochastic (matrix : Matrix ι ι R) : Prop :=
  (∀ i j, 0 ≤ matrix i j) ∧ ∀ i, (∑ j, matrix i j) ≤ 1

namespace IsRowSubstochastic

variable {matrix : Matrix ι ι R}

theorem nonneg (h : matrix.IsRowSubstochastic) (i j : ι) :
    0 ≤ matrix i j := h.1 i j

theorem rowSum_le_one (h : matrix.IsRowSubstochastic) (i : ι) :
    (∑ j, matrix i j) ≤ 1 := h.2 i

theorem of_mem_rowStochastic [DecidableEq ι] [IsOrderedRing R]
    {matrix : Matrix ι ι R} (h : matrix ∈ Matrix.rowStochastic R ι) :
    matrix.IsRowSubstochastic := by
  refine ⟨fun i j => Matrix.nonneg_of_mem_rowStochastic h, ?_⟩
  intro i
  exact (Matrix.sum_row_of_mem_rowStochastic h i).le

end IsRowSubstochastic

end Matrix

end

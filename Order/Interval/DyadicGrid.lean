/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.UniformGrid

/-!
# Finite dyadic refinements

This file specializes `UniformGrid` to grids with `2 ^ k` blocks on an
arbitrary interval in an ordered field. The interval endpoints are parameters;
unit-interval coordinates and their density are handled by a topology adapter.
Unbounded dyadic coordinates use Mathlib's `Dyadic` type.
-/

@[expose] public section

namespace DyadicGrid

/-- The number of dyadic blocks at level `k`. -/
def blocks (k : ℕ) : ℕ := 2 ^ k

/-- The level-`k` dyadic subdivision of an arbitrary ordered-field interval. -/
def grid {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (left right : K) (hleft : left ≤ right) (k : ℕ) : UniformGrid K where
  left := left
  right := right
  blocks := blocks k
  left_le_right := hleft
  blocks_pos := by
    dsimp [blocks]
    exact Nat.pow_pos (by decide)

/-- Consecutive dyadic subdivisions have the same endpoints and the finer
grid has twice as many blocks. -/
theorem isRefinement_succ {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (left right : K) (hleft : left ≤ right)
    (k : ℕ) :
    UniformGrid.IsRefinement (grid left right hleft k)
      (grid left right hleft (k + 1)) := by
  refine ⟨rfl, rfl, ?_⟩
  change blocks k ∣ blocks (k + 1)
  dsimp [blocks]
  rw [pow_succ]
  exact dvd_mul_right _ _

/-- The canonical embedding of level-`k` indices into level `k + 1` on the
same interval. -/
def lift {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (left right : K) (hleft : left ≤ right) (k : ℕ) :
    (grid left right hleft k).Index → (grid left right hleft (k + 1)).Index :=
  UniformGrid.refinementIndex (isRefinement_succ left right hleft k)

theorem point_lift {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (left right : K) (hleft : left ≤ right)
    (k : ℕ) (j : (grid left right hleft k).Index) :
    (grid left right hleft (k + 1)).point (lift left right hleft k j) =
      (grid left right hleft k).point j :=
  UniformGrid.point_refinement (isRefinement_succ left right hleft k) j

end DyadicGrid

end

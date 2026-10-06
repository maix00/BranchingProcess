/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalGrid.Interval

/-!
# Rational coordinates in the unit interval

This is the finite-grid specialization for rational time coordinates in
`[0, 1]`.  The general finite rational-coordinate bridge is in the parent
`RationalGrid` module.
-/

@[expose] public section

namespace RationalGrid

/-- Rational coordinates in the unit interval. -/
abbrev UnitCoordinate := Set.Icc (0 : ℚ) 1

/-- A finite family of rational unit-interval coordinates lies on one uniform
grid with endpoints `0` and `1`. -/
theorem exists_uniformGrid_of_unitCoordinateFinset
    (I : Finset UnitCoordinate) :
    ∃ grid : UniformGrid ℝ, grid.left = 0 ∧ grid.right = 1 ∧
      ∃ index : I → grid.Index,
      ∀ i : I, (i.1 : ℝ) = grid.point (index i) := by
  simpa using exists_uniformGrid_of_intervalFinset (left := 0) (right := 1)
    (by norm_num) I

end RationalGrid

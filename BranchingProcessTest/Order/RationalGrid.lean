import Order.Interval.RationalGrid

open UniformGrid

/-! Regression tests for finite rational grids beyond a fixed interval. -/

example :
    ∃ grid : UniformGrid ℝ,
      ∃ index : ({-2, 3} : Finset ℚ) → grid.Index,
        ∀ q, (q.1 : ℝ) = grid.point (index q) := by
  exact RationalGrid.exists_uniformGrid_of_finset _

example :
    ∃ grid : UniformGrid ℝ,
      ∃ index : (∅ : Finset ℚ) → grid.Index,
        ∀ q, (q.1 : ℝ) = grid.point (index q) := by
  exact RationalGrid.exists_uniformGrid_of_finset _

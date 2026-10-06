import Order.Interval.RationalGrid
import Order.Interval.RationalGrid.UnitInterval

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

example : ∃ grid : UniformGrid ℝ, grid.left = 0 ∧ grid.right = 1 := by
  let coordinates : Finset RationalGrid.UnitCoordinate :=
    {⟨0, by norm_num⟩, ⟨(1 / 3 : ℚ), by
      constructor
      · exact div_nonneg (by norm_num) (by norm_num)
      · exact (div_le_one (by norm_num : (0 : ℚ) < 3)).2 (by norm_num)⟩,
      ⟨1, by norm_num⟩}
  obtain ⟨grid, hleft, hright, _, _⟩ :=
    RationalGrid.exists_uniformGrid_of_unitCoordinateFinset coordinates
  exact ⟨grid, by simpa using hleft, by simpa using hright⟩

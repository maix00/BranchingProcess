import Order.Interval.UniformGrid

open UniformGrid

noncomputable def rationalUnitGrid : UniformGrid ℚ :=
  UniformGrid.unit (K := ℚ) 4 (by decide)

example : rationalUnitGrid.point ⟨2, by decide⟩ = (2 : ℚ) / 4 := by
  simpa [rationalUnitGrid] using
    (UniformGrid.unit_point (K := ℚ) 4 (by decide)
      (⟨2, by decide⟩ : (UniformGrid.unit (K := ℚ) 4 (by decide)).Index))

example (grid : UniformGrid ℚ) : grid.point (0 : grid.Index) = grid.left :=
  UniformGrid.point_zero grid

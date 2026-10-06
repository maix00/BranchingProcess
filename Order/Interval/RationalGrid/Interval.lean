/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Order.Interval.UniformGrid
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.Image
import Order.Interval.RationalGrid.Arithmetic

/-!
# Rational coordinates in bounded intervals

This module adapts the generic finite rational-coordinate grid theorem to an
interval with rational endpoints.  Its interval and unit-normalization
arithmetic is kept out of the root `RationalGrid` API.
-/

@[expose] public section

namespace RationalGrid

/-- Every finite family of rational points in a fixed bounded interval is
contained in a uniform grid with those interval endpoints. -/
theorem exists_uniformGrid_of_intervalFinset
    {left right : ℚ} (hleft : left ≤ right)
    (I : Finset (Set.Icc left right)) :
    ∃ grid : UniformGrid ℝ, grid.left = left ∧ grid.right = right ∧
      ∃ index : I → grid.Index,
      ∀ i : I, (i.1 : ℝ) = grid.point (index i) := by
  let J : Finset ℚ := I.attach.image (fun q => q.1)
  obtain ⟨grid, hgridLeft, hgridRight, index, hcoordinate⟩ :=
    Arithmetic.exists_uniformGrid_of_finset_mem_Icc hleft J (by
      intro q hq
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
      exact i.1.2)
  let index' (i : I) : grid.Index :=
    index ⟨i.1.1,
      Finset.mem_image.mpr ⟨i, Finset.mem_attach I i, rfl⟩⟩
  refine ⟨grid, hgridLeft, hgridRight, index', ?_⟩
  intro i
  exact hcoordinate ⟨i.1.1,
    Finset.mem_image.mpr ⟨i, Finset.mem_attach I i, rfl⟩⟩

end RationalGrid

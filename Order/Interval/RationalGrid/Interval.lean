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
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

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
  by_cases hEq : right = left
  · let grid : UniformGrid ℝ :=
      { left := left
        right := right
        blocks := 1
        left_le_right := by simpa using (Rat.cast_le (K := ℝ)).2 hleft
        blocks_pos := Nat.zero_lt_one }
    let index : I → grid.Index := fun _ => ⟨0, by simp [grid]⟩
    refine ⟨grid, rfl, rfl, index, fun i ↦ ?_⟩
    have hqi : i.1 = left := by
      apply le_antisymm
      · simpa [hEq] using i.1.2.2
      · exact i.1.2.1
    simp [grid, UniformGrid.point, index, hqi, hEq]
  · have hstrict : left < right := lt_of_le_of_ne hleft (Ne.symm hEq)
    let J : Finset ℚ := I.attach.image (fun q => Arithmetic.normalize left right q.1)
    obtain ⟨unitGrid, hunitLeft, hunitRight, unitIndex, hunit⟩ :=
      Arithmetic.exists_unit_uniformGrid_of_finset J (by
        intro q hq
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hq
        exact Arithmetic.normalize_mem_unit_interval hstrict x.1.2)
    let grid : UniformGrid ℝ :=
      { left := left
        right := right
        blocks := unitGrid.blocks
        left_le_right := by simpa using (Rat.cast_le (K := ℝ)).2 hleft
        blocks_pos := unitGrid.blocks_pos }
    let index : I → grid.Index := fun i ↦
      unitIndex ⟨Arithmetic.normalize left right i.1,
        Finset.mem_image.mpr ⟨i, Finset.mem_attach I i, rfl⟩⟩
    refine ⟨grid, rfl, rfl, index, fun i ↦ ?_⟩
    let j : J := ⟨Arithmetic.normalize left right i.1,
      Finset.mem_image.mpr ⟨i, Finset.mem_attach I i, rfl⟩⟩
    have hnormalized :
        (j.1 : ℝ) = unitGrid.point (unitIndex j) := hunit j
    have hunitcoord : (unitGrid.point (unitIndex j) : ℝ) =
        ((i.1 : ℚ) - left) / (right - left) := by
      rw [← hnormalized]
      change (Arithmetic.normalize left right i.1 : ℝ) = _
      simp [Arithmetic.normalize, Rat.cast_sub, Rat.cast_div]
    change (i.1 : ℝ) = grid.point (index i)
    rw [show grid.point (index i) =
        left + unitGrid.point (unitIndex j) * (right - left) by
      simp [grid, index, j, UniformGrid.point, hunitLeft, hunitRight]
      ]
    rw [hunitcoord]
    have hdenR' : (right : ℝ) - left ≠ 0 := by
      rw [← Rat.cast_sub]
      exact Rat.cast_ne_zero.mpr (sub_ne_zero.mpr hEq)
    rw [div_mul_cancel₀ _ hdenR']
    ring

end RationalGrid

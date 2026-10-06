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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Rat.Cast.Order
import Order.Interval.RationalGrid.Arithmetic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Finite rational-coordinate grids

This module exposes the generic bridge from a finite set of rational
coordinates to a real uniform grid.  Interval bounds and unit-interval
specializations live in dedicated adapter modules.
-/

@[expose] public section

namespace RationalGrid

/-- Every finite set of rational coordinates is represented on one finite
uniform grid on the real line. -/
theorem exists_uniformGrid_of_finset (I : Finset ℚ) :
    ∃ grid : UniformGrid ℝ, ∃ index : I → grid.Index,
      ∀ q : I, (q.1 : ℝ) = grid.point (index q) := by
  classical
  by_cases hI : I.Nonempty
  · let left := I.min' hI
    let right := I.max' hI
    have hleft : left ≤ right := Finset.min'_le_max' I hI
    by_cases hEq : right = left
    · let grid : UniformGrid ℝ :=
        { left := left
          right := right
          blocks := 1
          left_le_right := by simpa using (Rat.cast_le (K := ℝ)).2 hleft
          blocks_pos := Nat.zero_lt_one }
      let index : I → grid.Index := fun _ => ⟨0, by simp [grid]⟩
      refine ⟨grid, index, fun q ↦ ?_⟩
      have hq : q.1 = left := by
        apply le_antisymm
        · simpa [right, hEq] using Finset.le_max' I q.1 q.2
        · exact Finset.min'_le I q.1 q.2
      simp [grid, UniformGrid.point, index, hq, hEq]
    · have hstrict : left < right := lt_of_le_of_ne hleft (Ne.symm hEq)
      let normalized (q : I) := Arithmetic.normalize left right q.1
      let coordinates : Finset ℚ :=
        I.attach.image (fun q => Arithmetic.normalize left right q.1)
      have hcoordinates : ∀ q ∈ coordinates, 0 ≤ q ∧ q ≤ 1 := by
        intro q hq
        obtain ⟨x, _, hqx⟩ := Finset.mem_image.mp hq
        rw [← hqx]
        exact Arithmetic.normalize_mem_unit_interval hstrict
          ⟨Finset.min'_le I x.1 x.2, Finset.le_max' I x.1 x.2⟩
      obtain ⟨unitGrid, hunitLeft, hunitRight, unitIndex, hunit⟩ :=
        Arithmetic.exists_unit_uniformGrid_of_finset coordinates hcoordinates
      let grid : UniformGrid ℝ :=
        { left := left
          right := right
          blocks := unitGrid.blocks
          left_le_right := by simpa using (Rat.cast_le (K := ℝ)).2 hleft
          blocks_pos := unitGrid.blocks_pos }
      let index (q : I) : grid.Index :=
        unitIndex ⟨normalized q,
          Finset.mem_image.mpr ⟨q, Finset.mem_attach I q, rfl⟩⟩
      refine ⟨grid, index, fun q ↦ ?_⟩
      let j : coordinates := ⟨normalized q,
        Finset.mem_image.mpr ⟨q, Finset.mem_attach I q, rfl⟩⟩
      have hnormalized :
          (j.1 : ℝ) = unitGrid.point (unitIndex j) := hunit j
      have hunitcoord : (unitGrid.point (unitIndex j) : ℝ) =
          ((q.1 : ℚ) - left) / (right - left) := by
        rw [← hnormalized]
        change (Arithmetic.normalize left right q.1 : ℝ) = _
        simp [Arithmetic.normalize]
      change (q.1 : ℝ) = grid.point (index q)
      rw [show grid.point (index q) =
          left + unitGrid.point (unitIndex j) * (right - left) by
        simp [grid, index, j, UniformGrid.point, hunitLeft, hunitRight]]
      rw [hunitcoord]
      have hden : (right : ℝ) - left ≠ 0 := by
        rw [← Rat.cast_sub]
        exact Rat.cast_ne_zero.mpr (sub_ne_zero.mpr hEq)
      rw [div_mul_cancel₀ _ hden]
      ring
  · have hEmpty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    subst I
    refine ⟨UniformGrid.unit (K := ℝ) 1 (by decide), ?_, ?_⟩
    · intro q
      exact False.elim (Finset.notMem_empty q.1 q.property)
    · intro q
      exact False.elim (Finset.notMem_empty q.1 q.property)

end RationalGrid

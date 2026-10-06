/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Order.Interval.UniformGrid
import Mathlib.Data.Finset.Max
import Order.Interval.RationalGrid.Arithmetic

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
    obtain ⟨grid, _, _, index, hgrid⟩ :=
      Arithmetic.exists_uniformGrid_of_finset_mem_Icc hleft I (by
        intro q hq
        exact ⟨Finset.min'_le I q hq, Finset.le_max' I q hq⟩)
    exact ⟨grid, index, hgrid⟩
  · have hEmpty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    subst I
    let grid : UniformGrid ℝ :=
      { left := 0
        right := 0
        blocks := 1
        left_le_right := le_rfl
        blocks_pos := by decide }
    refine ⟨grid, ?_, ?_⟩
    · intro q
      exact False.elim (Finset.notMem_empty q.1 q.property)
    · intro q
      exact False.elim (Finset.notMem_empty q.1 q.property)

end RationalGrid

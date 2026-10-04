/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Finite uniform grids

`UniformGrid` is a deterministic finite affine grid on a bounded real
interval.  The interval endpoints are part of the object, so the common grid
`j / m` on `[0, 1]` is only one adapter.  A grid on an unbounded time axis is a
different object and is intentionally not identified with this finite grid.
-/

@[expose] public section

open Set

/-- A finite uniform grid on a real interval. -/
structure UniformGrid where
  left : ℝ
  right : ℝ
  blocks : ℕ
  left_le_right : left ≤ right
  blocks_pos : 0 < blocks

namespace UniformGrid

/-- The finite index type of a uniform grid. -/
abbrev Index (grid : UniformGrid) := Fin (grid.blocks + 1)

/-- The `j`-th point of a uniform grid. -/
noncomputable def point (grid : UniformGrid) (j : grid.Index) : ℝ :=
  grid.left + (j : ℝ) / (grid.blocks : ℝ) * (grid.right - grid.left)

@[simp]
theorem point_zero (grid : UniformGrid) :
    grid.point (0 : grid.Index) = grid.left := by
  simp [point]

@[simp]
theorem point_last (grid : UniformGrid) :
    grid.point ⟨grid.blocks, Nat.lt_succ_self _⟩ = grid.right := by
  have hblocks : (grid.blocks : ℝ) ≠ 0 := by
    exact_mod_cast grid.blocks_pos.ne'
  simp only [point]
  field_simp
  ring

theorem point_mem_Icc (grid : UniformGrid) (j : grid.Index) :
    grid.point j ∈ Icc grid.left grid.right := by
  have hblocks : 0 < (grid.blocks : ℝ) := by
    exact_mod_cast grid.blocks_pos
  have hj_nonneg : 0 ≤ (j : ℝ) := by positivity
  have hj_le : (j : ℝ) ≤ (grid.blocks : ℝ) := by
    exact_mod_cast j.is_le
  have hratio_nonneg : 0 ≤ (j : ℝ) / (grid.blocks : ℝ) :=
    div_nonneg hj_nonneg hblocks.le
  have hratio_le : (j : ℝ) / (grid.blocks : ℝ) ≤ 1 :=
    (div_le_one hblocks).2 hj_le
  constructor
  · exact le_add_of_nonneg_right
      (mul_nonneg hratio_nonneg (sub_nonneg.mpr grid.left_le_right))
  · rw [← sub_nonneg]
    calc
      grid.right - grid.point j =
          (1 - (j : ℝ) / (grid.blocks : ℝ)) *
            (grid.right - grid.left) := by
        simp only [point]
        ring
      _ ≥ 0 := mul_nonneg (sub_nonneg.mpr hratio_le)
        (sub_nonneg.mpr grid.left_le_right)

theorem monotone_point (grid : UniformGrid) :
    Monotone grid.point := by
  intro i j hij
  have hblocks : 0 < (grid.blocks : ℝ) := by
    exact_mod_cast grid.blocks_pos
  have hratio : (i : ℝ) / (grid.blocks : ℝ) ≤
      (j : ℝ) / (grid.blocks : ℝ) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hblocks.le
  simpa [point, add_comm] using add_le_add_left
    (mul_le_mul_of_nonneg_right hratio (sub_nonneg.mpr grid.left_le_right))
    grid.left

theorem strictMono_point {grid : UniformGrid}
    (hstrict : grid.left < grid.right) :
    StrictMono grid.point := by
  intro i j hij
  have hblocks : 0 < (grid.blocks : ℝ) := by
    exact_mod_cast grid.blocks_pos
  have hratio : (i : ℝ) / (grid.blocks : ℝ) <
      (j : ℝ) / (grid.blocks : ℝ) := by
    exact div_lt_div_of_pos_right (by exact_mod_cast hij) hblocks
  simpa [point, add_comm] using add_lt_add_left
    (mul_lt_mul_of_pos_right hratio (sub_pos.mpr hstrict)) grid.left

/-- The standard grid on the unit interval. -/
def unit (blocks : ℕ) (hblocks : 0 < blocks) : UniformGrid :=
  { left := 0
    right := 1
    blocks := blocks
    left_le_right := by norm_num
    blocks_pos := hblocks }

@[simp]
theorem unit_left (blocks : ℕ) (hblocks : 0 < blocks) :
    (unit blocks hblocks).left = 0 := rfl

@[simp]
theorem unit_right (blocks : ℕ) (hblocks : 0 < blocks) :
    (unit blocks hblocks).right = 1 := rfl

theorem unit_point (blocks : ℕ) (hblocks : 0 < blocks)
    (j : (unit blocks hblocks).Index) :
    (unit blocks hblocks).point j = (j : ℝ) / blocks := by
  simp [point, unit]

/-- `fine` refines `coarse` when it has the same endpoints and a divisible
number of blocks. -/
def IsRefinement (coarse fine : UniformGrid) : Prop :=
  coarse.left = fine.left ∧ coarse.right = fine.right ∧
    coarse.blocks ∣ fine.blocks

theorem isRefinement_refl (grid : UniformGrid) :
    IsRefinement grid grid := by
  exact ⟨rfl, rfl, dvd_rfl⟩

/-- The canonical inclusion of coarse grid indices into a refining grid. -/
def refinementIndex {coarse fine : UniformGrid} (h : IsRefinement coarse fine)
    (j : coarse.Index) : fine.Index :=
  ⟨j.val * (fine.blocks / coarse.blocks), by
    have hmul : coarse.blocks * (fine.blocks / coarse.blocks) = fine.blocks :=
      Nat.mul_div_cancel' h.2.2
    calc
      j.val * (fine.blocks / coarse.blocks) ≤
          coarse.blocks * (fine.blocks / coarse.blocks) := by
        exact Nat.mul_le_mul_right _ j.is_le
      _ = fine.blocks := hmul
      _ < fine.blocks + 1 := Nat.lt_succ_self _⟩

theorem point_refinement {coarse fine : UniformGrid}
    (h : IsRefinement coarse fine) (j : coarse.Index) :
    fine.point (refinementIndex h j) = coarse.point j := by
  have hcoarse : (coarse.blocks : ℝ) ≠ 0 := by
    exact_mod_cast coarse.blocks_pos.ne'
  have hfine : (fine.blocks : ℝ) ≠ 0 := by
    exact_mod_cast fine.blocks_pos.ne'
  have hmul : coarse.blocks * (fine.blocks / coarse.blocks) = fine.blocks :=
    Nat.mul_div_cancel' h.2.2
  simp only [point, refinementIndex]
  rw [h.1, h.2.1]
  push_cast
  field_simp [hcoarse, hfine]
  have hmulR : ((fine.blocks / coarse.blocks : ℕ) : ℝ) * coarse.blocks = fine.blocks := by
    rw [← Nat.cast_mul]
    exact_mod_cast (by simpa [Nat.mul_comm] using hmul)
  have haux :
      (j : ℝ) * ((fine.blocks / coarse.blocks : ℕ) : ℝ) *
          (fine.right - fine.left) * coarse.blocks =
        (j : ℝ) * fine.blocks * (fine.right - fine.left) := by
    calc
      (j : ℝ) * ((fine.blocks / coarse.blocks : ℕ) : ℝ) *
          (fine.right - fine.left) * coarse.blocks =
          (j : ℝ) * (((fine.blocks / coarse.blocks : ℕ) : ℝ) * coarse.blocks) *
            (fine.right - fine.left) := by ring
      _ = (j : ℝ) * fine.blocks * (fine.right - fine.left) := by
        rw [hmulR]
  calc
    _ = fine.left * fine.blocks * coarse.blocks +
          (j : ℝ) * ((fine.blocks / coarse.blocks : ℕ) : ℝ) *
            (fine.right - fine.left) * coarse.blocks := by ring
    _ = fine.blocks * (fine.left * coarse.blocks +
          (j : ℝ) * (fine.right - fine.left)) := by
      rw [haux]
      ring

end UniformGrid

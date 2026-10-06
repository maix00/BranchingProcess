/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import Mathlib.Order.Interval.Set.Basic

/-!
# Finite uniform grids

`UniformGrid` is a deterministic finite affine grid on an interval in a linear
ordered field. The interval endpoints are parameters, so the grid on `[0, 1]`
is one specialization. Infinite lattices on an unbounded axis are a different
object and are not identified with this finite interval grid.
-/

@[expose] public section

open Set

/-- A finite uniform grid on an interval in an ordered field. -/
structure UniformGrid (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  left : K
  right : K
  blocks : ℕ
  left_le_right : left ≤ right
  blocks_pos : 0 < blocks

namespace UniformGrid

/-- The finite index type of a uniform grid. -/
abbrev Index {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (grid : UniformGrid K) :=
  Fin (grid.blocks + 1)

/-- The `j`-th point of a uniform grid. -/
noncomputable def point {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (grid : UniformGrid K) (j : grid.Index) : K :=
  grid.left + (j : K) / (grid.blocks : K) * (grid.right - grid.left)

@[simp]
theorem point_zero {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (grid : UniformGrid K) :
    grid.point (0 : grid.Index) = grid.left := by
  simp [point]

@[simp]
theorem point_last {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (grid : UniformGrid K) :
    grid.point ⟨grid.blocks, Nat.lt_succ_self _⟩ = grid.right := by
  have hblocks : (grid.blocks : K) ≠ 0 := by
    exact_mod_cast grid.blocks_pos.ne'
  simp only [point]
  field_simp
  ring

theorem point_mem_Icc {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (grid : UniformGrid K) (j : grid.Index) :
    grid.point j ∈ Icc grid.left grid.right := by
  have hblocks : 0 < (grid.blocks : K) := by
    exact_mod_cast grid.blocks_pos
  have hj_nonneg : 0 ≤ (j : K) := by positivity
  have hj_le : (j : K) ≤ (grid.blocks : K) := by
    exact_mod_cast j.is_le
  have hratio_nonneg : 0 ≤ (j : K) / (grid.blocks : K) :=
    div_nonneg hj_nonneg hblocks.le
  have hratio_le : (j : K) / (grid.blocks : K) ≤ 1 :=
    (div_le_one hblocks).2 hj_le
  constructor
  · exact le_add_of_nonneg_right
      (mul_nonneg hratio_nonneg (sub_nonneg.mpr grid.left_le_right))
  · rw [← sub_nonneg]
    calc
      grid.right - grid.point j =
          (1 - (j : K) / (grid.blocks : K)) *
            (grid.right - grid.left) := by
        simp only [point]
        ring
      _ ≥ 0 := mul_nonneg (sub_nonneg.mpr hratio_le)
        (sub_nonneg.mpr grid.left_le_right)

theorem monotone_point {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (grid : UniformGrid K) :
    Monotone grid.point := by
  intro i j hij
  have hblocks : 0 < (grid.blocks : K) := by
    exact_mod_cast grid.blocks_pos
  have hratio : (i : K) / (grid.blocks : K) ≤
      (j : K) / (grid.blocks : K) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hblocks.le
  simpa [point, add_comm] using add_le_add_left
    (mul_le_mul_of_nonneg_right hratio (sub_nonneg.mpr grid.left_le_right))
    grid.left

theorem strictMono_point {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {grid : UniformGrid K}
    (hstrict : grid.left < grid.right) :
    StrictMono grid.point := by
  intro i j hij
  have hblocks : 0 < (grid.blocks : K) := by
    exact_mod_cast grid.blocks_pos
  have hratio : (i : K) / (grid.blocks : K) <
      (j : K) / (grid.blocks : K) := by
    exact div_lt_div_of_pos_right (by exact_mod_cast hij) hblocks
  simpa [point, add_comm] using add_lt_add_left
    (mul_lt_mul_of_pos_right hratio (sub_pos.mpr hstrict)) grid.left

/-- The standard grid on the unit interval. -/
def unit {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (blocks : ℕ) (hblocks : 0 < blocks) : UniformGrid K :=
  { left := 0
    right := 1
    blocks := blocks
    left_le_right := zero_le_one
    blocks_pos := hblocks }

@[simp]
theorem unit_left {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (blocks : ℕ) (hblocks : 0 < blocks) :
    (unit blocks hblocks).left = (0 : K) := rfl

@[simp]
theorem unit_right {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (blocks : ℕ) (hblocks : 0 < blocks) :
    (unit blocks hblocks).right = (1 : K) := rfl

theorem unit_point {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (blocks : ℕ) (hblocks : 0 < blocks)
    (j : (unit blocks hblocks).Index) :
    (unit blocks hblocks).point j = (j : K) / blocks := by
  simp [point, unit]

/-- `fine` refines `coarse` when it has the same endpoints and a divisible
number of blocks. -/
def IsRefinement {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (coarse fine : UniformGrid K) : Prop :=
  coarse.left = fine.left ∧ coarse.right = fine.right ∧
    coarse.blocks ∣ fine.blocks

theorem isRefinement_refl {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (grid : UniformGrid K) :
    IsRefinement grid grid := by
  exact ⟨rfl, rfl, dvd_rfl⟩

/-- The canonical inclusion of coarse grid indices into a refining grid. -/
def refinementIndex {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {coarse fine : UniformGrid K} (h : IsRefinement coarse fine)
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

theorem point_refinement {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {coarse fine : UniformGrid K}
    (h : IsRefinement coarse fine) (j : coarse.Index) :
    fine.point (refinementIndex h j) = coarse.point j := by
  have hcoarse : (coarse.blocks : K) ≠ 0 := by
    exact_mod_cast coarse.blocks_pos.ne'
  have hfine : (fine.blocks : K) ≠ 0 := by
    exact_mod_cast fine.blocks_pos.ne'
  have hmul : coarse.blocks * (fine.blocks / coarse.blocks) = fine.blocks :=
    Nat.mul_div_cancel' h.2.2
  simp only [point, refinementIndex]
  rw [h.1, h.2.1]
  push_cast
  field_simp [hcoarse, hfine]
  have hmulR : ((fine.blocks / coarse.blocks : ℕ) : K) * coarse.blocks = fine.blocks := by
    rw [← Nat.cast_mul]
    exact_mod_cast (by simpa [Nat.mul_comm] using hmul)
  have haux :
      (j : K) * ((fine.blocks / coarse.blocks : ℕ) : K) *
          (fine.right - fine.left) * coarse.blocks =
        (j : K) * fine.blocks * (fine.right - fine.left) := by
    calc
      (j : K) * ((fine.blocks / coarse.blocks : ℕ) : K) *
          (fine.right - fine.left) * coarse.blocks =
          (j : K) * (((fine.blocks / coarse.blocks : ℕ) : K) * coarse.blocks) *
            (fine.right - fine.left) := by ring
      _ = (j : K) * fine.blocks * (fine.right - fine.left) := by
        rw [hmulR]
  calc
    _ = fine.left * fine.blocks * coarse.blocks +
          (j : K) * ((fine.blocks / coarse.blocks : ℕ) : K) *
            (fine.right - fine.left) * coarse.blocks := by ring
    _ = fine.blocks * (fine.left * coarse.blocks +
          (j : K) * (fine.right - fine.left)) := by
      rw [haux]
      ring

end UniformGrid

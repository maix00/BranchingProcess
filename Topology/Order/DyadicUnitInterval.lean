/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Topology.UnitInterval
public import Order.Interval.DyadicGrid

/-!
# Dyadic coordinates in the unit interval

This is the unit-interval topological adapter for the finite dyadic grids.
The underlying `DyadicGrid.grid` accepts arbitrary endpoints; this file adds
the unit-interval subtype and its density theorem.
-/

@[expose] public section

open Set

namespace DyadicGrid

/-- The level-`k` dyadic grid specialized to the real unit interval. -/
noncomputable def unitGrid (k : ℕ) : UniformGrid ℝ :=
  grid 0 1 (by norm_num) k

/-- A dyadic grid point viewed as a point of the real unit interval. -/
noncomputable def unitPoint (k : ℕ) (j : (unitGrid k).Index) : unitInterval :=
  ⟨(unitGrid k).point j, by
    simpa [unitGrid, DyadicGrid.grid] using
      UniformGrid.point_mem_Icc (unitGrid k) j⟩

/-- The dyadic coordinate set in the real unit interval. -/
def unitPoints : Set unitInterval := ⋃ k, Set.range (unitPoint k)

theorem countable_unitPoints : unitPoints.Countable := by
  unfold unitPoints
  exact Set.countable_iUnion fun k => Set.countable_range _

private theorem unitGrid_point (k : ℕ) (j : (unitGrid k).Index) :
    (unitGrid k).point j = (j : ℝ) / blocks k := by
  simp [unitGrid, DyadicGrid.grid, DyadicGrid.blocks, UniformGrid.point]

theorem dense_unitPoints : Dense unitPoints := by
  rw [Metric.dense_iff]
  intro x ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  let k := n + 1
  let N := blocks k
  have hN : 0 < N := by
    dsimp [N, blocks]
    positivity
  have hnN : n + 1 ≤ N := by
    dsimp [N, k, blocks]
    exact (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hNε : (1 : ℝ) / N < ε := by
    have hNcast : (n + 1 : ℝ) ≤ N := by exact_mod_cast hnN
    exact lt_of_le_of_lt
      (one_div_le_one_div_of_le (by positivity) hNcast) hn
  let y : ℕ := Nat.floor ((x : ℝ) * N)
  have hx_nonneg : 0 ≤ (x : ℝ) := x.property.1
  have hy_nonneg : 0 ≤ (x : ℝ) * N := by positivity
  have hy_le : y ≤ N := by
    have hy_le_real : (y : ℝ) ≤ (N : ℝ) := by
      calc
        (y : ℝ) ≤ (x : ℝ) * N := Nat.floor_le hy_nonneg
        _ ≤ (1 : ℝ) * N := mul_le_mul_of_nonneg_right x.property.2 (by positivity)
        _ = N := one_mul _
    exact_mod_cast hy_le_real
  let j : (unitGrid k).Index := ⟨y, by
    change y < N + 1
    exact Nat.lt_succ_of_le hy_le⟩
  have hy_upper : (x : ℝ) * N < (y : ℝ) + 1 := by
    simpa [y] using Nat.lt_floor_add_one ((x : ℝ) * N)
  have hpoint_le : (unitGrid k).point j ≤ (x : ℝ) := by
    rw [unitGrid_point, show blocks k = N by rfl]
    apply (div_le_iff₀ (by exact_mod_cast hN)).2
    simpa [j, y] using Nat.floor_le hy_nonneg
  have hupper_point : (x : ℝ) < (unitGrid k).point j + (1 : ℝ) / N := by
    rw [unitGrid_point, show blocks k = N by rfl]
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have := (lt_div_iff₀ hNreal).2 hy_upper
    simpa [j, y, add_div] using this
  refine ⟨unitPoint k j, ?_, mem_iUnion.mpr ⟨k, mem_range.mpr ⟨j, rfl⟩⟩⟩
  change dist (unitPoint k j) x < ε
  rw [Subtype.dist_eq, Real.dist_eq]
  change |(unitGrid k).point j - (x : ℝ)| < ε
  apply abs_lt.2
  constructor
  · linarith
  · exact lt_of_le_of_lt (sub_nonpos.mpr hpoint_le) hε

end DyadicGrid

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Algebra.Order.Floor
public import Topology.Cadlag.Basic

/-!
# Càdlàg regularity of floor maps

The integer and natural floor maps are right-continuous and have left limits.
These deterministic facts are independent of random walks and belong to the
order-topology layer.
-/

@[expose] public section

open Filter Set
open scoped Topology

/-- The integer floor function is càdlàg on the real line. -/
theorem IsCadlag.floor_int : IsCadlag (fun x : ℝ => ⌊x⌋) where
  isRightContinuous := by
    intro x
    exact ((tendsto_floor_right_pure_floor x).mono_left
      (nhdsWithin_mono x Set.Ioi_subset_Ici_self)).mono_right (pure_le_nhds _)
  tendsto_nhdsLT x := by
    refine ⟨⌈x⌉ - 1, ?_⟩
    exact (tendsto_floor_left_pure_ceil_sub_one x).mono_right
      (pure_le_nhds _)

/-- The natural-valued floor function is càdlàg on the real line. -/
theorem IsCadlag.floor_nat : IsCadlag (fun x : ℝ => ⌊x⌋₊) := by
  have h := IsCadlag.floor_int.continuous_comp
    (continuous_of_discreteTopology : Continuous (Int.toNat : ℤ → ℕ))
  convert h using 1
  funext x
  exact Int.floor_toNat x

end

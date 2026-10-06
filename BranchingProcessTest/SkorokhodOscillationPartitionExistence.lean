/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Topology.Cadlag.Skorokhod.Oscillation.Partition.Existence

#print axioms Skorokhod.IsCadlag.exists_oscillation_partition
#print axioms Skorokhod.CadlagPath.exists_admits_oscillation_partition

private inductive PseudoTarget where
  | first
  | second

private instance : PseudoMetricSpace PseudoTarget where
  dist _ _ := 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  dist_triangle _ _ _ := by simp

example : ∃ partition : Skorokhod.OscillationPartition, ∃ bound : ℝ,
    bound < 1 ∧ Skorokhod.OscillationBoundedOnPartition partition
      (⟨fun _ : unitInterval => PseudoTarget.first, IsCadlag.const⟩ :
        CadlagPath unitInterval PseudoTarget) bound := by
  exact Skorokhod.IsCadlag.exists_oscillation_partition
    (f := fun _ : unitInterval => PseudoTarget.first) IsCadlag.const (by norm_num)

example (partition : Skorokhod.OscillationPartition)
    (path : CadlagPath unitInterval PseudoTarget)
    {bound : ℝ}
    (hosc : Skorokhod.OscillationBoundedOnPartition partition path bound) :
    Skorokhod.OscillationBoundedOnPartition
      (partition.pullback Skorokhod.TimeChange.refl 0
        (by linarith [partition.mesh_pos]) (by intro t; simp)) path bound := by
  simpa using
    (Skorokhod.OscillationBoundedOnPartition.pullback
      partition Skorokhod.TimeChange.refl 0 0
      (by linarith [partition.mesh_pos]) (by intro t; simp)
      path path (by intro t; simp) hosc)

example :
    ∃ partition : Skorokhod.OscillationPartition, ∃ bound : ℝ,
      bound < 1 ∧ Skorokhod.OscillationBoundedOnPartition partition
        (⟨fun _ : unitInterval => 0, IsCadlag.const⟩ :
          CadlagPath unitInterval ℝ) bound := by
  exact Skorokhod.IsCadlag.exists_oscillation_partition
    (f := fun _ : unitInterval => 0) IsCadlag.const (by norm_num)

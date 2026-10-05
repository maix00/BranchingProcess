/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Topology.Cadlag.Skorokhod.Oscillation.Partition.Existence

#print axioms Skorokhod.IsCadlag.exists_oscillation_partition
#print axioms Skorokhod.CadlagPath.exists_admits_oscillation_partition

example :
    ∃ partition : Skorokhod.OscillationPartition, ∃ bound : ℝ,
      bound < 1 ∧ Skorokhod.OscillationBoundedOnPartition partition
        (⟨fun _ : unitInterval => 0, IsCadlag.const⟩ :
          CadlagPath unitInterval ℝ) bound := by
  exact Skorokhod.IsCadlag.exists_oscillation_partition
    (f := fun _ : unitInterval => 0) IsCadlag.const (by norm_num)

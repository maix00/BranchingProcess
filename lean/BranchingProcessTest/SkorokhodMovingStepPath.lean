/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Topology.Cadlag.Skorokhod.Compactness.Approximation

#print axioms Skorokhod.IsSeparatedPartitionPoints.strictMono
#print axioms Skorokhod.isClosed_setOf_isSeparatedPartitionPoints
#print axioms Skorokhod.isCompact_setOf_isSeparatedPartitionPoints
#print axioms Skorokhod.j1EDist_stepPath_le_ofMatchingPartitions_value
#print axioms Skorokhod.isCompact_setOf_stepPathParameters
#print axioms Skorokhod.stepPathOfParameters
#print axioms Skorokhod.j1EDist_stepPathOfParameters_le
#print axioms Skorokhod.continuous_stepPathOfParameters
#print axioms Skorokhod.isCompact_stepPathOfParameters_image
#print axioms Skorokhod.OscillationPartition.stepApproximation_eq_ofPoints_stepPath
#print axioms Skorokhod.boundedMovingPartitionStepPathFamily
#print axioms Skorokhod.isCompact_boundedMovingPartitionStepPathFamily
#print axioms Skorokhod.OscillationPartition.stepApproximation_mem_boundedMovingPartitionStepPathFamily
#print axioms Skorokhod.totallyBounded_of_uniform_admitsOscillationPartition

example {n : ℕ} (hn : 0 < n) {gap bound : ℝ} (hgap : 0 < gap) :
    IsCompact (Set.range (Skorokhod.stepPathOfParameters hn
      (gap := gap) (bound := bound) hgap)) :=
  Skorokhod.isCompact_stepPathOfParameters_image hn hgap

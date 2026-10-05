/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Topology.Cadlag.Skorokhod.Oscillation.Partition.Finite
import Topology.Cadlag.Skorokhod.Oscillation.Partition.Measurability

#print axioms Skorokhod.OscillationPartition.isCadlag_stepFunction
#print axioms IsCadlag.updateTop
#print axioms Skorokhod.OscillationPartition.ofFinitePoints
#print axioms Skorokhod.OscillationPartition.stepPath
#print axioms Skorokhod.OscillationPartition.stepApproximation
#print axioms Skorokhod.OscillationPartition.index_eq_of_cell
#print axioms Skorokhod.OscillationPartition.index_monotone
#print axioms Skorokhod.OscillationPartition.pullback
#print axioms Skorokhod.OscillationPartition.size_mul_mesh_le_one
#print axioms Skorokhod.OscillationPartition.dist_stepApproximation_le
#print axioms Skorokhod.OscillationPartition.uniformEDist_stepApproximation_le
#print axioms Skorokhod.OscillationPartition.j1EDist_stepApproximation_le
#print axioms Skorokhod.OscillationBoundedOnPartition.pullback
#print axioms Skorokhod.isOpen_admitsOscillationPartition
#print axioms Skorokhod.measurableSet_admitsOscillationPartition

namespace Skorokhod

private def oneCellPoints : Fin 2 → unitInterval := fun i =>
  if i.val = 0 then ⊥ else ⊤

private theorem oneCellPoints_strict : StrictMono oneCellPoints := by
  intro i j hij
  have hi : i.val = 0 := by omega
  have hj : j.val = 1 := by omega
  simp [oneCellPoints, hi, hj]

private noncomputable def oneCellPartition : OscillationPartition :=
  OscillationPartition.ofFinitePoints (by omega) oneCellPoints
    (by simp [oneCellPoints]) (by simp [oneCellPoints]) oneCellPoints_strict

private noncomputable def terminalJump : CadlagPath unitInterval ℝ := by
  classical
  letI : DecidableEq (↥unitInterval) := inferInstance
  refine ⟨fun t => if t = ⊤ then 1 else 0, ?_⟩
  exact IsCadlag.const.updateTop 1

example : terminalJump ⊤ = 1 := by simp [terminalJump]

example {t : unitInterval} (ht : t ≠ ⊤) : terminalJump t = 0 := by
  simp [terminalJump, ht]

example : OscillationBoundedOnPartition oneCellPartition terminalJump 0 := by
  intro s t hs ht _
  simp [terminalJump, hs, ht]

end Skorokhod

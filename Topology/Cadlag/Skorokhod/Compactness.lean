/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Compactness.Compact
public import Topology.Cadlag.Skorokhod.Oscillation.Partition.Basic

/-!
# Compact families of fixed-partition step paths

For a fixed finite time partition, the map from its finite vector of values to
the associated càdlàg step path is nonexpansive from the supremum metric to
the Skorokhod `J₁` metric. Consequently, restricting every value to a compact
subset of the state space gives a compact family of paths.

This finite-dimensional compactness result is one ingredient for a general
Skorokhod compactness criterion; it does not state that criterion.
-/

@[expose] public section

open Filter

namespace Skorokhod

/-- The fixed-partition step-path map does not increase the extended distance.
The identity time change bounds `J₁` by uniform distance, and the latter is
bounded by the supremum distance between the finite vectors of values. -/
theorem OscillationPartition.edist_stepPath_le
    {E : Type*} [MetricSpace E] (partition : OscillationPartition)
    (v w : Fin partition.size → E) :
    edist (partition.stepPath v) (partition.stepPath w) ≤ edist v w := by
  rw [edist_cadlagPath_eq_j1EDist]
  refine (j1EDist_le_uniformEDist _ _).trans ?_
  rw [uniformEDist_eq_edist, UniformFun.edist_def]
  apply iSup_le
  intro t
  exact (edist_le_pi_edist v w (partition.index t))

/-- The fixed-partition step-path map is continuous for the `J₁` topology. -/
theorem OscillationPartition.continuous_stepPath
    {E : Type*} [MetricSpace E] (partition : OscillationPartition) :
    Continuous (fun v : Fin partition.size → E => partition.stepPath v) := by
  rw [continuous_iff_continuousAt]
  intro v
  rw [ContinuousAt, tendsto_iff_edist_tendsto_0]
  have hsource : Tendsto (fun w : Fin partition.size → E => edist w v)
      (nhds v) (nhds 0) :=
    tendsto_iff_edist_tendsto_0.1 continuousAt_id
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsource
  · exact Eventually.of_forall fun _ => bot_le
  · exact Eventually.of_forall fun w =>
      partition.edist_stepPath_le w v

/-- Step paths on a fixed finite partition whose values lie in a compact set
form a compact subset of Skorokhod space. -/
theorem OscillationPartition.isCompact_stepPath_image
    {E : Type*} [MetricSpace E] (partition : OscillationPartition)
    {K : Set E} (hK : IsCompact K) :
    IsCompact
      ((fun v : Fin partition.size → E => partition.stepPath v) ''
        Set.pi Set.univ (fun _ : Fin partition.size => K)) := by
  apply (isCompact_univ_pi fun _ => hK).image
  exact partition.continuous_stepPath

end Skorokhod

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Oscillation.Partition.Pullback

/-!
# Measurability of oscillation-partition path sets

The existence of a finite partition with strict minimum-gap and within-cell-oscillation margins is open in the Skorokhod `J₁` topology, hence Borel measurable.
-/

@[expose] public section

open Set
open scoped ENNReal Topology

namespace Skorokhod


/-- Paths admitting a finite partition with a strict lower bound on cell
length and a strict upper bound on within-cell oscillation. -/
def admitsOscillationPartition {E : Type*} [MetricSpace E]
    (minimumGap maximumOscillation : ℝ) :
    Set (CadlagPath unitInterval E) :=
  {path | ∃ partition : OscillationPartition,
    minimumGap < partition.mesh ∧
      ∃ bound < maximumOscillation,
        OscillationBoundedOnPartition partition path bound}

/-- Admitting a partition with strict mesh and oscillation margins is an open
property for the Skorokhod `J₁` topology. -/
theorem isOpen_admitsOscillationPartition {E : Type*} [MetricSpace E]
    (minimumGap maximumOscillation : ℝ) :
    IsOpen (admitsOscillationPartition (E := E) minimumGap maximumOscillation) := by
  rw [isOpen_iff_forall_mem_open]
  intro path hpath
  obtain ⟨partition, hgap, bound, hbound, hosc⟩ := hpath
  have hmeshPos := partition.mesh_pos
  let error := min (partition.mesh / 4)
    (min ((partition.mesh - minimumGap) / 4)
      ((maximumOscillation - bound) / 4))
  have hgapMargin : 0 < partition.mesh - minimumGap := sub_pos.mpr hgap
  have hboundMargin : 0 < maximumOscillation - bound := sub_pos.mpr hbound
  have herror : 0 < error := by
    dsimp [error]
    positivity
  refine ⟨Metric.ball path error, ?_, Metric.isOpen_ball,
    Metric.mem_ball_self herror⟩
  intro other hother
  have hj1 : j1EDist path other < ENNReal.ofReal error := by
    rw [← edist_cadlagPath_eq_j1EDist, edist_dist,
      ENNReal.ofReal_lt_ofReal_iff herror]
    simpa [dist_comm] using Metric.mem_ball.mp hother
  obtain ⟨change, hcost⟩ := exists_timeChange_j1Cost_lt hj1
  have hdistortion : change.distortion < error := by
    have hpart : ENNReal.ofReal change.distortion < ENNReal.ofReal error :=
      (le_max_left _ _).trans_lt hcost
    exact (ENNReal.ofReal_lt_ofReal_iff herror).1 hpart
  have huniform : uniformEDist (change.act path) other < ENNReal.ofReal error :=
    (le_max_right _ _).trans_lt hcost
  have htime (t : unitInterval) : dist (change t) t ≤ error :=
    (TimeChange.dist_apply_le_distortion change t).trans hdistortion.le
  have hspace (t : unitInterval) : dist (change.act path t) (other t) ≤ error := by
    have hpoint :=
      (edist_apply_le_uniformEDist (change.act path) other t).trans_lt huniform
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff herror] at hpoint
    exact hpoint.le
  have herrorMesh : error ≤ partition.mesh / 4 := min_le_left _ _
  have herrorGap : error ≤ (partition.mesh - minimumGap) / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have herrorOsc : error ≤ (maximumOscillation - bound) / 4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hmesh : 2 * error < partition.mesh := by
    nlinarith [partition.mesh_pos]
  let pulled := partition.pullback change error hmesh htime
  have hgap' : minimumGap < pulled.mesh := by
    dsimp [pulled, OscillationPartition.pullback]
    nlinarith
  have hbound' : bound + 2 * error < maximumOscillation := by
    nlinarith
  exact ⟨pulled, hgap', bound + 2 * error, hbound',
    OscillationBoundedOnPartition.pullback partition change error error hmesh
      htime path other hspace hosc⟩

theorem measurableSet_admitsOscillationPartition
    {E : Type*} [MetricSpace E] (minimumGap maximumOscillation : ℝ) :
    MeasurableSet (admitsOscillationPartition (E := E) minimumGap maximumOscillation) :=
  (isOpen_admitsOscillationPartition (E := E) minimumGap maximumOscillation).measurableSet

/-- A sequence of positive mesh and oscillation thresholds defines the event
that every level admits a matching finite oscillation partition. -/
def admitsOscillationPartitionSequence {E : Type*} [MetricSpace E]
    (minimumGap maximumOscillation : ℕ → ℝ) :
    Set (CadlagPath unitInterval E) :=
  ⋂ n : ℕ, admitsOscillationPartition (minimumGap n) (maximumOscillation n)

/-- The multiscale oscillation-partition event is Borel measurable. -/
theorem measurableSet_admitsOscillationPartitionSequence
    {E : Type*} [MetricSpace E] (minimumGap maximumOscillation : ℕ → ℝ) :
    MeasurableSet (admitsOscillationPartitionSequence (E := E)
      minimumGap maximumOscillation) := by
  exact MeasurableSet.iInter fun n =>
    measurableSet_admitsOscillationPartition (minimumGap n) (maximumOscillation n)

end Skorokhod

end

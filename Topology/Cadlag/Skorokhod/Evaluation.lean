/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Topology
public import Topology.Cadlag.Skorokhod.Separation

/-!
# Evaluation maps in the Skorokhod topology

Coordinate evaluation is continuous at every path that is continuous at the
selected time. This is the continuity input for finite-dimensional
identification of weak limits on càdlàg path space.
-/

@[expose] public section

open scoped ENNReal Topology

namespace Skorokhod

/-- Evaluation at a time is continuous at any path continuous at that time
for the Skorokhod `J₁` topology. -/
theorem continuousAt_apply_of_continuousAt {E : Type*} [MetricSpace E]
    (f : CadlagPath unitInterval E) (t : unitInterval)
    (hf : ContinuousAt f t) :
    ContinuousAt (fun g : CadlagPath unitInterval E => g t) f := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hf' := Metric.continuousAt_iff.mp hf
  obtain ⟨δ, hδ, hcontrol⟩ := hf' (ε / 2) (half_pos hε)
  let r := min δ (ε / 2)
  have hr : 0 < r := lt_min hδ (by positivity)
  refine ⟨r, hr, fun g hfg => ?_⟩
  have hdist : dist f g < r := by
    simpa [dist_comm] using hfg
  have hj1 : j1EDist f g < ENNReal.ofReal r := by
    rw [← edist_cadlagPath_eq_j1EDist, edist_dist,
      ENNReal.ofReal_lt_ofReal_iff hr]
    exact hdist
  obtain ⟨change, hchange⟩ := exists_timeChange_j1Cost_lt hj1
  have hclockENN : ENNReal.ofReal change.distortion < ENNReal.ofReal r :=
    (le_max_left _ _).trans_lt hchange
  have hclock : change.distortion < r :=
    (ENNReal.ofReal_lt_ofReal_iff hr).1 hclockENN
  have htime : dist (change t) t < r :=
    (change.dist_apply_le_distortion t).trans_lt hclock
  have htime' : dist (change t) t < δ :=
    htime.trans_le (min_le_left _ _)
  have hvalue : dist (f (change t)) (f t) < ε / 2 :=
    hcontrol htime'
  have huniform : uniformEDist (change.act f) g < ENNReal.ofReal r :=
    (le_max_right _ _).trans_lt hchange
  have hpointENN :=
    (edist_apply_le_uniformEDist (change.act f) g t).trans_lt huniform
  have hpoint : dist (f (change t)) (g t) < r := by
    rw [TimeChange.act_apply, edist_dist,
      ENNReal.ofReal_lt_ofReal_iff hr] at hpointENN
    exact hpointENN
  have hpoint' : dist (g t) (f (change t)) < ε / 2 := by
    calc
      dist (g t) (f (change t)) = dist (f (change t)) (g t) := dist_comm _ _
      _ < r := hpoint
      _ ≤ ε / 2 := min_le_right _ _
  calc
    dist (g t) (f t) ≤
        dist (g t) (f (change t)) + dist (f (change t)) (f t) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hpoint' hvalue
    _ = ε := by ring

end Skorokhod

end

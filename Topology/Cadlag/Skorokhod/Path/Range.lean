/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Range
public import Topology.Cadlag.Skorokhod.Topology

/-!
# State-space range conditions in Skorokhod path space

This file proves topological properties of the common-range path set in the
Skorokhod `J₁` topology. The underlying set is defined generically in
`Topology.Cadlag.Range`.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace Skorokhod

/-- A closed state-space range gives a closed set in the Skorokhod `J₁`
path space. -/
theorem isClosed_rangeIn {E : Type*} [MetricSpace E] {range : Set E}
    (hrange : IsClosed range) :
    IsClosed (CadlagPath.rangeIn (T := unitInterval) range) := by
  classical
  change IsClosed {path : CadlagPath unitInterval E | ∀ t, path t ∈ range}
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro path hpath
  have hnot : ∃ t : unitInterval, path t ∉ range := by
    change ¬ ∀ t : unitInterval, path t ∈ range at hpath
    exact not_forall.mp hpath
  obtain ⟨t, ht⟩ := hnot
  have hopen : IsOpen rangeᶜ := hrange.isOpen_compl
  obtain ⟨radius, hradius, hball⟩ :=
    Metric.isOpen_iff.mp hopen (path t) ht
  refine ⟨Metric.ball path radius, ?_, Metric.isOpen_ball,
    Metric.mem_ball_self hradius⟩
  intro other hother
  have hj1 : j1EDist path other < ENNReal.ofReal radius := by
    rw [← edist_cadlagPath_eq_j1EDist, edist_dist,
      ENNReal.ofReal_lt_ofReal_iff hradius]
    simpa [dist_comm] using Metric.mem_ball.mp hother
  obtain ⟨change, hchange⟩ := exists_timeChange_j1Cost_lt hj1
  have huniform : uniformEDist (change.act path) other <
      ENNReal.ofReal radius :=
    (le_max_right _ _).trans_lt hchange
  let s := change.symm t
  have hs := (edist_apply_le_uniformEDist
    (change.act path) other s).trans_lt huniform
  rw [TimeChange.act_apply, TimeChange.apply_symm_apply] at hs
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hradius] at hs
  have hnotRange : other s ∉ range :=
    hball (Metric.mem_ball.mpr (by simpa [dist_comm] using hs))
  intro hall
  exact hnotRange (hall s)

/-- The common-range path set is Borel when the state-space range is closed. -/
theorem measurableSet_rangeIn {E : Type*} [MetricSpace E] {range : Set E}
    (hrange : IsClosed range) :
    MeasurableSet (CadlagPath.rangeIn (T := unitInterval) range) :=
  (isClosed_rangeIn hrange).measurableSet

end Skorokhod

end

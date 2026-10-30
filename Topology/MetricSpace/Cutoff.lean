/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Continuous cutoffs for open sets in metric spaces

## Public declarations

- `Metric.openSetCutoff s x`: the distance from `x` to `sᶜ`, capped at `1`,
  namely `min 1 (Metric.infDist x sᶜ)`.
- `Metric.continuous_openSetCutoff`: the cutoff is continuous in `x`.
- `Metric.openSetCutoff_nonneg` and `Metric.openSetCutoff_le_one`: its values
  lie in `[0,1]`.
- `Metric.openSetCutoff_pos_iff`: if `s` is open and `sᶜ` is nonempty, the
  cutoff is positive exactly on `s`.

The definition uses Mathlib's continuous distance-to-a-set function; the
openness hypothesis identifies the positive set with `s` itself.
-/

@[expose] public section

namespace Metric

/-- The distance from a point to the complement of `s`, capped at `1`. -/
noncomputable def openSetCutoff {α : Type*} [PseudoMetricSpace α]
    (s : Set α) (x : α) : ℝ :=
  min 1 (infDist x sᶜ)

theorem continuous_openSetCutoff {α : Type*} [PseudoMetricSpace α]
    (s : Set α) : Continuous (openSetCutoff s) := by
  unfold openSetCutoff
  exact continuous_const.min (continuous_infDist_pt _)

theorem openSetCutoff_nonneg {α : Type*} [PseudoMetricSpace α]
    (s : Set α) (x : α) : 0 ≤ openSetCutoff s x :=
  le_min (by norm_num) infDist_nonneg

theorem openSetCutoff_le_one {α : Type*} [PseudoMetricSpace α]
    (s : Set α) (x : α) : openSetCutoff s x ≤ 1 :=
  min_le_left _ _

theorem openSetCutoff_pos_iff {α : Type*} [PseudoMetricSpace α]
    {s : Set α} (hs : IsOpen s) (hcompl : sᶜ.Nonempty) (x : α) :
    0 < openSetCutoff s x ↔ x ∈ s := by
  constructor
  · intro h
    have hdist : 0 < infDist x sᶜ := (lt_min_iff.mp h).2
    have hnot : x ∉ closure sᶜ :=
      (infDist_pos_iff_notMem_closure hcompl).mpr hdist
    by_contra hmem
    exact hnot (subset_closure hmem)
  · intro hmem
    have hnot : x ∉ closure sᶜ := by
      rw [hs.isClosed_compl.closure_eq]
      simpa using hmem
    have hdist : 0 < infDist x sᶜ :=
      (infDist_pos_iff_notMem_closure hcompl).mp hnot
    exact lt_min zero_lt_one hdist

end Metric

end

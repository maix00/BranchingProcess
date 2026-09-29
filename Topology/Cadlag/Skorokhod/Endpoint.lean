import Mathlib.Topology.UnitInterval
import Topology.Cadlag.Skorokhod.Topology

/-!
# Endpoint evaluation in the Skorokhod topology

Evaluation need not be continuous at an interior time for the `J₁` topology.
It is continuous at the terminal time because every admissible time change
fixes that endpoint.
-/

open Set
open scoped ENNReal Topology

namespace Skorokhod

/-- Terminal evaluation is nonexpansive for the Skorokhod `J₁` metric. -/
theorem dist_apply_top_le {E : Type*} [MetricSpace E]
    (f g : CadlagPath unitInterval E) :
    dist (f ⊤) (g ⊤) ≤ dist f g := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro ε hε
  have hεpos : 0 < ε := lt_of_le_of_lt (dist_nonneg : 0 ≤ dist f g) hε
  have hj1 : j1EDist f g < ENNReal.ofReal ε := by
    rw [← edist_cadlagPath_eq_j1EDist, edist_dist,
      ENNReal.ofReal_lt_ofReal_iff hεpos]
    exact hε
  obtain ⟨change, hchange⟩ := exists_timeChange_j1Cost_lt hj1
  have huniform : uniformEDist (change.act f) g < ENNReal.ofReal ε :=
    (le_max_right _ _).trans_lt hchange
  have hpoint :=
    (edist_apply_le_uniformEDist (change.act f) g ⊤).trans_lt huniform
  rw [TimeChange.act_apply, TimeChange.apply_top, edist_dist,
    ENNReal.ofReal_lt_ofReal_iff hεpos] at hpoint
  exact hpoint.le

/-- Evaluation at the terminal time is continuous in the Skorokhod `J₁`
topology. -/
theorem continuous_apply_top {E : Type*} [MetricSpace E] :
    Continuous (fun path : CadlagPath unitInterval E => path ⊤) := by
  apply continuous_iff_continuousAt.2
  intro f
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε, hε, fun g hfg => ?_⟩
  exact (dist_apply_top_le g f).trans_lt hfg

/-- Evaluation at the initial time is nonexpansive for the Skorokhod `J₁`
metric. -/
theorem dist_apply_bot_le {E : Type*} [MetricSpace E]
    (f g : CadlagPath unitInterval E) :
    dist (f ⊥) (g ⊥) ≤ dist f g := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro ε hε
  have hεpos : 0 < ε := lt_of_le_of_lt (dist_nonneg : 0 ≤ dist f g) hε
  have hj1 : j1EDist f g < ENNReal.ofReal ε := by
    rw [← edist_cadlagPath_eq_j1EDist, edist_dist,
      ENNReal.ofReal_lt_ofReal_iff hεpos]
    exact hε
  obtain ⟨change, hchange⟩ := exists_timeChange_j1Cost_lt hj1
  have huniform : uniformEDist (change.act f) g < ENNReal.ofReal ε :=
    (le_max_right _ _).trans_lt hchange
  have hpoint :=
    (edist_apply_le_uniformEDist (change.act f) g ⊥).trans_lt huniform
  rw [TimeChange.act_apply, TimeChange.apply_bot, edist_dist,
    ENNReal.ofReal_lt_ofReal_iff hεpos] at hpoint
  exact hpoint.le

/-- Evaluation at the initial time is continuous in the Skorokhod `J₁`
topology. -/
theorem continuous_apply_bot {E : Type*} [MetricSpace E] :
    Continuous (fun path : CadlagPath unitInterval E => path ⊥) := by
  apply continuous_iff_continuousAt.2
  intro f
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε, hε, fun g hfg => ?_⟩
  exact (dist_apply_bot_le g f).trans_lt hfg

end Skorokhod

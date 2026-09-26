import Combinatorics.UlamHarris.Tree.Finite.Basic
import Combinatorics.UlamHarris.Tree.Metric

/-!
# The space of finite trees

This file equips `FiniteTree α` with:

* the default topology, the subspace topology of the pointwise topology on
  `Tree α`;
* the measurable structure, the subspace σ-algebra of the cylinder σ-algebra
  on `Tree α`;
* the restriction of the tree metric, and the topology it induces.

As for all trees, the metric and its topology are named structures rather than
global instances, so the default topology stays the subspace of the pointwise
topology.
-/

open MeasureTheory
open scoped Topology

namespace Combinatorics

namespace UlamHarris

namespace Tree

namespace Finite

variable {α : Type*} [LT α]

/-- The default topology on finite trees: the subspace topology of the
pointwise topology on `Tree α`. -/
@[instance_reducible]
def topology (α : Type*) [LT α] : TopologicalSpace (FiniteTree α) :=
  (treePointwiseTopology (α := α)).induced Subtype.val

/-- The measurable structure on finite trees: the subspace σ-algebra of the
cylinder σ-algebra on `Tree α`. -/
@[instance_reducible]
def measurableSpace (α : Type*) [LT α] : MeasurableSpace (FiniteTree α) :=
  (instMeasurableSpaceTree (α := α)).comap Subtype.val

/-- The tree metric restricted to finite trees. It is a named structure, not a
global instance. -/
@[instance_reducible]
noncomputable def metricSpace (α : Type*) [LT α] : MetricSpace (FiniteTree α) :=
  MetricSpace.induced Subtype.val Subtype.val_injective (treeMetricSpace α)

/-- The topology induced by the restricted tree metric. -/
@[instance_reducible]
noncomputable def metricTopology (α : Type*) [LT α] : TopologicalSpace (FiniteTree α) :=
  (metricSpace α).toUniformSpace.toTopologicalSpace

theorem topology_eq_inst (α : Type*) [LT α] :
    topology α = (inferInstance : TopologicalSpace (FiniteTree α)) :=
  rfl

theorem measurableSpace_eq_inst (α : Type*) [LT α] :
    measurableSpace α = (inferInstance : MeasurableSpace (FiniteTree α)) :=
  rfl

/-- The metric topology is the subspace topology of the truncation/metric
topology on `Tree α`. -/
theorem metricTopology_eq_induced (α : Type*) [LT α] :
    metricTopology α = (treeMetricTopology α).induced Subtype.val :=
  rfl

/-- The metric topology is finer than the default pointwise topology. -/
theorem metricTopology_le_topology (α : Type*) [LT α] :
    metricTopology α ≤ topology α := by
  have h : treeMetricTopology α ≤ treePointwiseTopology (α := α) := by
    rw [treeMetricTopology_eq_truncationTopology]
    exact treeTruncationTopology_le_pointwise
  rw [metricTopology_eq_induced, topology]
  exact induced_mono (g := Subtype.val) h

/-- For a countable label type, the Borel σ-algebra of the default topology is
the cylinder σ-algebra on finite trees. -/
theorem borel_topology_eq_measurableSpace [Countable α] :
    @borel (FiniteTree α) (topology α) = measurableSpace α := by
  rw [topology, borel_comap, borel_treePointwiseTopology_eq_cylinder]
  rfl

/-- The cylinder σ-algebra on finite trees is contained in the Borel σ-algebra
of the restricted tree metric. -/
theorem measurableSpace_le_borel_metricTopology [Countable α] :
    measurableSpace α ≤ @borel (FiniteTree α) (metricTopology α) := by
  rw [metricTopology_eq_induced, borel_comap, measurableSpace]
  exact MeasurableSpace.comap_mono cylinder_le_borel_treeMetricTopology

/-- If the ambient truncation balls are countable, then the Borel σ-algebra of
the restricted tree metric is the cylinder σ-algebra on finite trees. -/
theorem borel_metricTopology_eq_measurableSpace_of_countable_balls [Countable α]
    (hball : Countable {b : Set (Tree α) // ∃ T n, b = Tree.truncationBall T n}) :
    @borel (FiniteTree α) (metricTopology α) = measurableSpace α := by
  rw [metricTopology_eq_induced, borel_comap, measurableSpace,
    borel_treeMetricTopology_eq_borel_treeTruncationTopology,
    borel_treeTruncationTopology_eq_cylinder_of_countable_balls hball]

end Finite

end Tree

end UlamHarris

end Combinatorics

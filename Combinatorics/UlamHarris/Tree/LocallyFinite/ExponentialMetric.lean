/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module
public import Combinatorics.UlamHarris.Tree.LocallyFinite.Borel

/-!
# Exponential depth metric on locally finite trees

## Public declarations

In namespace `Combinatorics.UlamHarris.Tree.LocallyFinite`:

* `expMetricSpace` restricts $d(T,T')=\exp(-m)$ at first differing generation $m$;
  `expMetricTopology` is its topology.
* `expMetricTopology_eq_metricTopology` identifies exponential and reciprocal
  depth topologies on locally finite trees.
* `completeSpace_expMetricSpace` proves completeness of exponential depth distance.
* `finiteTrees_denseRange_expMetricTopology` gives finite-tree density for this metric.
* `borel_expMetricTopology_eq_measurableSpace` identifies its Borel sigma algebra
  with the membership-cylinder sigma algebra for countable child labels.

These are the depth-topology properties of the rooted trees used in
J. Neveu, "Arbres et processus de Galton--Watson", Section 2,
*Annales de l'I.H.P. Probabilités et statistiques* 22(2) (1986), 199--207,
https://www.numdam.org/item/AIHPB_1986__22_2_199_0/.
-/
@[expose] public section
namespace Combinatorics.UlamHarris.Tree.LocallyFinite

/-- Restrict exponential depth distance to locally finite trees. -/
@[instance_reducible]
noncomputable def expMetricSpace (α : Type*) [LT α] : MetricSpace (LocallyFiniteTree α) :=
  MetricSpace.induced Subtype.val Subtype.val_injective (expTreeMetricSpace α)

/-- The associated topology, without changing the default tree topology. -/
@[instance_reducible]
noncomputable def expMetricTopology (α : Type*) [LT α] : TopologicalSpace (LocallyFiniteTree α) :=
  (expMetricSpace α).toUniformSpace.toTopologicalSpace

/-- Both metrics induce the same topology on the locally finite subspace. -/
theorem expMetricTopology_eq_metricTopology (α : Type*) [LT α] :
    expMetricTopology α = metricTopology α := by
  change (expTreeMetricTopology α).induced Subtype.val =
    (treeMetricTopology α).induced Subtype.val
  rw [expTreeMetricTopology_eq_treeMetricTopology]

/-- Locally finite trees form a complete exponential-depth metric space. -/
theorem completeSpace_expMetricSpace (α : Type*) [LT α] :
    @CompleteSpace (LocallyFiniteTree α) (expMetricSpace α).toUniformSpace := by
  let : MetricSpace (Tree α) := expTreeMetricSpace α
  let : TopologicalSpace (Tree α) := expTreeMetricTopology α
  let : CompleteSpace (Tree α) := completeSpace_expTreeMetricSpace α
  have hc : @IsClosed (Tree α) (expTreeMetricTopology α) {T | T.IsLocallyFinite} := by
    rw [expTreeMetricTopology_eq_treeMetricTopology]
    exact isClosed_isLocallyFinite
  exact hc.isComplete.completeSpace_coe

/-- Finite trees are dense for exponential depth distance as well. -/
theorem finiteTrees_denseRange_expMetricTopology {α : Type*} [LT α] :
    @DenseRange (LocallyFiniteTree α) (expMetricTopology α) (FiniteTree α)
      (toLocallyFinite α) := by
  rw [expMetricTopology_eq_metricTopology]
  exact finiteTrees_denseRange

/-- Exponential-depth Borel sets are precisely the trace of membership cylinders. -/
theorem borel_expMetricTopology_eq_measurableSpace {α : Type*} [LT α] [Countable α] :
    @borel (LocallyFiniteTree α) (expMetricTopology α) = measurableSpace α := by
  rw [expMetricTopology_eq_metricTopology]
  exact borel_metricTopology_eq_measurableSpace

end Combinatorics.UlamHarris.Tree.LocallyFinite

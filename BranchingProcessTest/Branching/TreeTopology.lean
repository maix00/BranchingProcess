import Combinatorics.UlamHarris.Tree.Topology.Metric.Strictness
import Combinatorics.UlamHarris.Tree.LocallyFinite.ExponentialMetric
import Mathlib.Data.PNat.Basic

namespace Combinatorics.UlamHarris
open Combinatorics.UlamHarris.Tree

-- The chapter's exponential metric has the same Borel sets as reciprocal depth distance.
example : @borel (Tree ℕ) (expTreeMetricTopology ℕ) =
    @borel (Tree ℕ) (treeMetricTopology ℕ) :=
  borel_expTreeMetricTopology_eq_borel_treeMetricTopology ℕ

-- The full-tree Borel sigma algebra is strictly larger; the locally finite trace agrees.
example : instMeasurableSpaceTree (α := ℕ) < @borel (Tree ℕ) (expTreeMetricTopology ℕ) :=
  cylinder_lt_borel_expTreeMetricTopology

example : instMeasurableSpaceTree (α := ℕ+) <
    @borel (Tree ℕ+) (expTreeMetricTopology ℕ+) :=
  cylinder_lt_borel_expTreeMetricTopology

example : @borel (LocallyFiniteTree ℕ) (LocallyFinite.expMetricTopology ℕ) =
    LocallyFinite.measurableSpace ℕ := LocallyFinite.borel_expMetricTopology_eq_measurableSpace

example : @CompleteSpace (LocallyFiniteTree ℕ) (LocallyFinite.expMetricSpace ℕ).toUniformSpace :=
  LocallyFinite.completeSpace_expMetricSpace ℕ

#print axioms Combinatorics.UlamHarris.Tree.expTreeMetricTopology_eq_treeMetricTopology
#print axioms Combinatorics.UlamHarris.Tree.completeSpace_treeMetricSpace
#print axioms Combinatorics.UlamHarris.Tree.completeSpace_expTreeMetricSpace
#print axioms Combinatorics.UlamHarris.Tree.LocallyFinite.completeSpace_expMetricSpace
#print axioms Combinatorics.UlamHarris.Tree.LocallyFinite.finiteTrees_denseRange
#print axioms Combinatorics.UlamHarris.Tree.LocallyFinite.borel_expMetricTopology_eq_measurableSpace
#print axioms Combinatorics.UlamHarris.Tree.cylinder_lt_borel_expTreeMetricTopology

end Combinatorics.UlamHarris

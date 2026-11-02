import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Large
/-!
# Axiom audit for the selected-population large-drawdown estimate

The audit covers the raw-event reduction, its measurability input, and the
finite-horizon probability bound used in the polynomial endpoint sublevel proof.
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Spine.measurableSet_hasFirstPassageBelow

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Spine.measure_hasFirstPassageBelow_le

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.measure_selectedFirstPassageBelowByHorizon_le

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.rawFirstNSelectedLargeDrop_subset_firstNSelectedLargeDrawdown

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.measure_rawFirstNSelectedLargeDrop_le

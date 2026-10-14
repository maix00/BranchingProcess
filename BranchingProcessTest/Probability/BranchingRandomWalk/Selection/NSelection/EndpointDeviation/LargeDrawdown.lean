import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.LargeDrawdown
/-!
# Axiom audit for the selected-population large-drawdown estimate

The audit covers the raw-event reduction, its measurability input, and the
finite-horizon probability bound used in the polynomial endpoint sublevel proof.
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measurableSet_hasFirstPassageBelow

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_hasFirstPassageBelow_le

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_selectedFirstPassageBelowByHorizon_le

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rawFirstNSelectedLargeDrop_subset_firstNSelectedLargeDrawdown

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rawFirstNSelectedLargeDrop_le

import Probability.BranchingRandomWalk.Selection.Tail.LargeDrawdown

/-!
# Axiom audit for the selected-population large-drawdown estimate

The audit covers the raw-event reduction, its measurability input, and the
finite-horizon probability bound used in the polynomial left-tail proof.
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.Tail.measurableSet_hasFirstPassageBelow

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.Tail.measure_hasFirstPassageBelow_le

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.Tail.measure_selectedFirstPassageBelowByHorizon_le

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.Tail.rawFirstNSelectedLargeDrop_subset_firstNSelectedLargeDrawdown

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.Tail.measure_rawFirstNSelectedLargeDrop_le

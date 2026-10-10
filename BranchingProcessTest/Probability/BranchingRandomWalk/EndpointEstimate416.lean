import Probability.BranchingRandomWalk.Analytic.EndpointEstimate416

/-!
# Axiom audit for the finite-horizon Aïdékon--Hu endpoint estimate

The endpoint event is split pathwise using selected-population ancestor
closure, then estimated by the existing large-drawdown and one-root
many-to-one bounds.
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.measurableSet_firstNSelectedEndpointBelow

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.firstNSelectedEndpointBelow_subset_rawFirstNSelectedLargeDrop_union_noLargeDrop

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.measure_firstNSelectedEndpointBelow_le_ah416

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Population
/-!
# Axiom audit for the selected-population drawdown transfer

The transfer below covers the no-large-drawdown endpoint event at a fixed
generation.  It does not include the large-drawdown union term in (4.16).
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.firstNSelectedPopulation_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measurableSet_firstNSelectedNoLargeDropEndpointBelow

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.firstNSelectedPopulation_depth

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.firstNSelectedPopulation_surviveAlong

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.firstNSelectedNoLargeDropEndpointBelow_subset_roots

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_firstNSelectedNoLargeDropEndpointBelow_le

module

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.Splits

/-!
# Axiom audit for pre-sampled selected-path split completions
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.splitCount_eq_sum_indicators

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.splitCount_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.splitCompletion_isStoppingTime

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.decompose_at_split_field

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.mark_decompose_at_split_field

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.isAlive_decompose_at_split_field

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.GrowthTrial.root_at_recursive_split

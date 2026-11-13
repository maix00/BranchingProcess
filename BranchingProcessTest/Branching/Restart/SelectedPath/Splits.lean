module

import Probability.BranchingRandomWalk.Restart.SelectedPath.Splits

/-!
# Axiom audit for pre-sampled selected-path split completions
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.splitCount_eq_sum_indicators

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.splitCount_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.splitCompletion_isStoppingTime

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.decompose_at_split_field

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.mark_decompose_at_split_field

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.isAlive_decompose_at_split_field

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.root_at_recursive_split

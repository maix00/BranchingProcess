import Probability.BranchingRandomWalk.Restart.RootedTrial.SpineSplits

/-!
# Axiom audit for pre-sampled reserve-spine split completions
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineSplitCount_eq_sum_indicators

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineSplitCount_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineSplitCompletion_isStoppingTime

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpinePath_decompose_at_split_field

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineMark_decompose_at_split_field

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineAlive_decompose_at_split_field

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineCandidate_root_at_recursive_split

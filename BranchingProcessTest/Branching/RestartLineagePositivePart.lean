import Probability.BranchingRandomWalk.Restart.RootedTrial.PositivePart

/-!
# Axiom audit for the causal reserve-source positive-part estimate

The statements below are pathwise consequences of the reserve selector and
the live-spine inclusion.  In particular, the audit does not certify an iid
law for the marks sampled at the adaptive spine vertices.
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.reserveSpineSlot_potential_le_cutoff_add_firstChildPositive

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpinePath_potential_eq_sum_edges

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpinePath_positivePart_le_cutoff_add_firstChildSum

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartSourceSlice_contains_live_spine

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartSourceMinPosition_le_live_spine

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartSourceMinPosition_positivePart_le

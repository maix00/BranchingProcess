import Probability.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Lemmas.PositivePart

/-!
# Axiom audit for the selected-path BRW population positive-part estimate

The statements below are pathwise consequences of the reserve selector and
the live selected-path inclusion.  In particular, the audit does not certify an iid
law for the marks sampled at the adaptive selected path vertices.
-/

#print axioms
  Combinatorics.Branching.Step.FiniteSelection.potentialValue'_selectedContinuationSlot_le_cutoff_add_firstSelectedSlotPositive

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Lemmas.potential_eq_sum_edges

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Lemmas.positivePart_le_cutoff_add_firstSelectedChildSum

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Population.slice_contains_selectedPath

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Lemmas.minPosition_positivePart_le

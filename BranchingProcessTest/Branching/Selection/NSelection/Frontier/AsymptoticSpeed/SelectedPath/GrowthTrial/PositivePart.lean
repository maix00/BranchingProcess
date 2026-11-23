module

import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Lemmas.PositivePart

/-!
# Axiom audit for the selected-path BRW population positive-part estimate

The statements below are pathwise consequences of the first-or-below-potential selector and
the live selected-path inclusion.  In particular, the audit does not certify an iid
law for the marks sampled at the adaptive selected path vertices.
-/

#print axioms
  Combinatorics.Branching.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.potentialValue'_continuationSlot_le_cutoff_add_firstSelectedSlotPositive

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Lemmas.potential_eq_sum_edges

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Lemmas.positivePart_le_cutoff_add_firstSelectedChildSum

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Population.slice_contains_selectedPath

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Lemmas.minPosition_positivePart_le

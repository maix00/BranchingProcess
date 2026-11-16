import Probability.BranchingRandomWalk.Step.Selection.BoundedSplit

/-!
# Axiom audit for bounded edges at first-or-below-potential splits

The first-or-below-potential selector retains its first selected child without
a cutoff on every step. This test audits the stronger fact needed by the
selected-path argument: on a split,
the capacity-two ordered selector forces both selected edge potentials below
the cutoff.
-/

#print axioms
  Combinatorics.Branching.Step.FiniteSelection.firstOrBelowPotential_card_ge_two_iff_boundedSecond

#print axioms
  Combinatorics.Branching.Step.FiniteSelection.firstOrBelowPotential_edgePotentials_le_of_ordered

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Step.Selection.firstOrBelowPotential_split_edgePotentials_le_sorted_ae

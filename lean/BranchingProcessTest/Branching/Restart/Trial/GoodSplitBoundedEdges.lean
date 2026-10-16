import Probability.BranchingRandomWalk.Restart.GoodSplit

/-!
# Axiom audit for bounded edges at reserve splits

The reserve selector retains its first child without a cutoff on every step.
This test audits the stronger fact needed by the restart argument: on a split,
the capacity-two ordered selector forces both selected edge potentials below
the cutoff.
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.reserveSelectionBelowPotential_split_iff_boundedSecond

#print axioms
  ProbabilityTheory.BranchingRandomWalk.reserveSelectionBelowPotential_split_edgePotentials_le_of_ordered

#print axioms
  ProbabilityTheory.BranchingRandomWalk.reserveSelectionBelowPotential_split_edgePotentials_le_sorted_ae

import Probability.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Lemmas.Expectation

/-!
# Axiom audit for the integrated causal selected-path bound

The estimate is conditional on one-step first integrability and almost-sure
ordering/nonemptiness along the finite selected path.  It concerns the causal reserve
selected path only and does not identify it with the retrospectively restarted endpoint.
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Lemmas.integral_positivePart_le

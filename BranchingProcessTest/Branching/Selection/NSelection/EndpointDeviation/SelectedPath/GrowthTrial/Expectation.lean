import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.GrowthTrial.Lemmas.Expectation

/-!
# Axiom audit for the integrated causal selected-path bound

The estimate is conditional on one-step first integrability and almost-sure
ordering/nonemptiness along the finite selected path. It concerns the causal
selected path and does not identify it with the retrospectively restarted endpoint.
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.GrowthTrial.Lemmas.integral_positivePart_le

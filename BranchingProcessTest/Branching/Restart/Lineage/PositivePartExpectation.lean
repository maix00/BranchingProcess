import Probability.BranchingRandomWalk.Restart.RootedTrial.Reward.Expectation

/-!
# Axiom audit for the integrated causal reserve-spine bound

The estimate is conditional on one-step first integrability and almost-sure
ordering/nonemptiness along the finite spine.  It concerns the causal reserve
spine only and does not identify it with the retrospectively restarted endpoint.
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.integral_selectedReserveSpinePath_positivePart_le

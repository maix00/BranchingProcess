import Probability.BranchingRandomWalk.Restart.RootedTrial.PositivePartExpectation

/-!
# Axiom audit for the integrated causal reserve-spine bound

The estimate is conditional on one-step first integrability and almost-sure
ordering/nonemptiness along the finite spine.  It concerns the causal reserve
spine only and does not identify it with the thesis restart endpoint.
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.integral_selectedReserveSpinePath_positivePart_le

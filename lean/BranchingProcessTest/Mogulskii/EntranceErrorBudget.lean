import Probability.Process.RandomWalk.SmallDeviation.Entrance.ExponentialLoss

/-!
# Axiom audit for the finite-variance entrance error budget

This test checks the transfer from the polynomial cyclic-rotation lower bound
to the exponential error scale used on longer horizons.
-/

#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.exists_eventually_iidSequenceLaw_finiteMovingEntranceEvent_ge_exp_of_centeredSecondMoment

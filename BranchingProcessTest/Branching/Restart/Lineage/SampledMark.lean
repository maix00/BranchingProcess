import Probability.BranchingRandomWalk.Restart.RootedTrial.Coupling.SampledMark

/-!
# Axiom audit for reserve-spine step laws

The audit includes the iid law of the totalized adaptively sampled spine
sequence, obtained from each new step's independence of the preceding domain
flow.
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineFutureRoots_countable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineFutureRoots_fiber_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineFutureRoots_depth

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineFutureRoots_injective

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineStep_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineStep_law

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineStep_independent

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineStep_iIndepFun

#print axioms
  ProbabilityTheory.BranchingRandomWalk.integral_selectedReserveSpineStep_observable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.integral_selectedReserveSpineStep_firstRSelectedSlotPositivePotential

import Probability.BranchingRandomWalk.Restart.SelectedPath.Coupling.SampledMark

/-!
# Axiom audit for selected-path step laws

The audit includes the iid law of the totalized adaptively sampled selected path
sequence, obtained from each new step's independence of the preceding domain
flow.
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Coupling.futureRoots_countable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Coupling.futureRoots_fiber_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Coupling.futureRoots_depth

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Coupling.futureRoots_injective

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Coupling.step_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Coupling.step_law

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Coupling.step_independent

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Coupling.step_iIndepFun

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Coupling.integral_step_observable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Coupling.integral_step_firstSelectedSlotPositivePotential

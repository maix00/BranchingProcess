import Probability.Process.RandomWalk.Path.Skorokhod.Oscillation

#print axioms
  ProbabilityTheory.RandomWalk.normalizedStepCadlagPathIcc_oscillationBoundedOnStepPartition
#print axioms
  ProbabilityTheory.RandomWalk.exists_pos_uniform_admitsOscillationPartition_normalizedStepPath

example (scale : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (increment : ℕ → ℝ) :
    Skorokhod.OscillationBoundedOnPartition
      (ProbabilityTheory.RandomWalk.normalizedStepOscillationPartition n hn)
      (ProbabilityTheory.RandomWalk.normalizedStepCadlagPathIcc scale n increment) 0 :=
  ProbabilityTheory.RandomWalk.normalizedStepCadlagPathIcc_oscillationBoundedOnStepPartition
    scale n hn increment

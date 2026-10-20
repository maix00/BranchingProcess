import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLaw.Process

/-!
# Source-derived stable process existence audit

The construction theorem takes scalar attraction and path-law tightness as
inputs; it does not assume a pre-existing stable Lévy process.
-/

#print axioms
  ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.exists_stableLevyProcess_of_tightSource

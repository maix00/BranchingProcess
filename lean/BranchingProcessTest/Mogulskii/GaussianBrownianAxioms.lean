import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Gaussian.SourcePathClass

/-!
# Axiom audit for the Gaussian stable-process bridge

These declarations audit the proof from a Mathlib `IsBrownianReal` input to
the exponent-two stable process, its unit-interval path law, and the explicit
source-path rate. They do not construct an inhabitant of `IsBrownianReal`.
The separate `BrownianMotion` package contains a canonical construction, but
its pinned revision currently does not build against this repository's pinned
Mathlib; see `MOGULSKII_STABLE_MAPPING.md`.
-/

#print axioms ProbabilityTheory.IsPreBrownianReal.hasStableClockIncrements
#print axioms ProbabilityTheory.IsBrownianReal.isStableLevyProcess
#print axioms ProbabilityTheory.IsBrownianReal.isStableClockProcessLaw_cadlagunitIntervalProcessPathLaw
#print axioms ProbabilityTheory.IsStableLevyProcess.unitIntervalPathLaw
#print axioms ProbabilityTheory.IsStableLevyProcess.isStableClockProcessLaw_unitIntervalPathLaw
#print axioms ProbabilityTheory.HasStableProcessEscapeRate.eq_neg_pi_sq_div_eight
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_source_index_two_of_brownian_explicit

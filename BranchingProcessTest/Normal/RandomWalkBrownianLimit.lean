import Probability.Process.RandomWalk.FunctionalLimit.Normal.PathLimit.Brownian

/-!
# Brownian realization axiom checks

This test prints the axioms used by the scalar Gaussian domain-of-attraction
result, the Brownian path-law construction, and the resulting normalized
random-walk path limit.
-/

#print axioms ProbabilityTheory.isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_unitSecondMoment
#print axioms ProbabilityTheory.Process.Path.Cadlag.aemeasurable_pathMap
#print axioms ProbabilityTheory.IsBrownianReal.isStableClockProcessLaw_cadlagunitIntervalProcessPathLaw
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Normal.tendsto_normalizedStepPathLaw_of_gaussian_of_brownian
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Normal.tendsto_normalizedStepCadlagPathIcc_of_centeredUnitSecondMoment_of_brownian

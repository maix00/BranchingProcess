import Probability.Distributions.CharacteristicFunction.Tauberian.SecondTail
import Probability.Distributions.Stable.Attraction.NormingRatios.Tauberian

/-! Check the proof dependencies at the boundary between the abstract cosine
defect, the second-tail identity, and stable-domain regular variation. -/

#print axioms ProbabilityTheory.secondTailIntegral_eq_cosineDefect_kernel
#print axioms
  ProbabilityTheory.IsInDomainOfAttractionAlong.isRegularlyVarying_symmetrizedCosineDefect

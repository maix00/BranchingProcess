import Probability.Process.RandomWalk.Path.Skorokhod.Tightness

open MeasureTheory

#print axioms ProbabilityTheory.RandomWalk.isTightMeasureSet_singleton_normalizedStepPathLaw
#print axioms
  ProbabilityTheory.RandomWalk.isTightMeasureSet_normalizedStepPathLaw_image_of_finite

example (ν : Measure ℝ) [IsProbabilityMeasure ν] (scale : ℕ → ℝ)
    {I : Set ℕ} (hI : I.Finite) :
    MeasureTheory.IsTightMeasureSet
      (ProbabilityTheory.RandomWalk.normalizedStepPathLaw ν scale '' I) :=
  ProbabilityTheory.RandomWalk.isTightMeasureSet_normalizedStepPathLaw_image_of_finite
    ν scale hI

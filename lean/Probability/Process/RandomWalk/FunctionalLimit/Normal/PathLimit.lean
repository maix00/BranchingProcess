/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Normal.Tightness
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLimit
public import Probability.Process.Stable.Brownian.PathLaw

/-!
# Functional limits in the normal domain of attraction

The scalar Gaussian-domain assumption supplies finite-dimensional convergence,
and the normal-domain estimates supply `J₁` tightness. The target remains an
explicit Brownian path law with the stable-clock increment specification; this
keeps the functional theorem independent of a particular Brownian construction.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Normal

/-- The centered normal-domain random walk converges in the Skorokhod `J₁`
topology to any standard Brownian path law. The source law may have infinite
variance: tightness follows from the truncated-second-moment estimates, and
the Gaussian domain-of-attraction hypothesis supplies the finite-dimensional
limits. -/
theorem tendsto_normalizedStepPathLaw_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization (fun _ => 0))
    (hnormalization : ∀ n, 0 < n → 0 < normalization n)
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw 2 (gaussianReal 0 1)
      unitIntervalClock P) :
    Tendsto (fun n : ℕ =>
      (⟨RandomWalk.normalizedStepPathLaw ν normalization n,
        (inferInstance : IsProbabilityMeasure
          (RandomWalk.normalizedStepPathLaw ν normalization n))⟩ :
        ProbabilityMeasure (CadlagPath unitInterval ℝ)))
      atTop (@nhds (ProbabilityMeasure (CadlagPath unitInterval ℝ)) inferInstance
    (⟨P, (inferInstance : IsProbabilityMeasure P)⟩ :
          ProbabilityMeasure (CadlagPath unitInterval ℝ))) := by
  exact RandomWalk.FunctionalLimit.Stable.tendsto_normalizedStepPathLaw_of_zeroCenter_stableDomain_of_tight
    hDOA hP
    (isTightMeasureSet_range_normalizedStepPathLaw_of_gaussian
      hDOA hnormalization)

/-- Source-level exponent-two functional limit for a chosen pointwise-
continuous Brownian version. The source increments may have infinite
variance. The pointwise continuity hypothesis is required by the current
measurable continuous-path embedding; Mathlib's `IsBrownianReal` itself only
asserts almost-sure continuity. -/
theorem tendsto_normalizedStepPathLaw_of_gaussian_of_preBrownian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization (fun _ => 0))
    (hnormalization : ∀ n, 0 < n → 0 < normalization n)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    Tendsto (fun n : ℕ =>
      (⟨RandomWalk.normalizedStepPathLaw ν normalization n,
        (inferInstance : IsProbabilityMeasure
          (RandomWalk.normalizedStepPathLaw ν normalization n))⟩ :
        ProbabilityMeasure (CadlagPath unitInterval ℝ)))
      atTop (@nhds (ProbabilityMeasure (CadlagPath unitInterval ℝ)) inferInstance
        (⟨cadlagunitIntervalPathLaw P B hcontinuous hmeasurable,
          (inferInstance : IsProbabilityMeasure
            (cadlagunitIntervalPathLaw P B hcontinuous hmeasurable))⟩ :
          ProbabilityMeasure (CadlagPath unitInterval ℝ))) := by
  exact tendsto_normalizedStepPathLaw_of_gaussian hDOA hnormalization
    (hB.isStableClockProcessLaw_cadlagunitIntervalPathLaw
      hcontinuous hmeasurable)

end ProbabilityTheory.RandomWalk.FunctionalLimit.Normal

end

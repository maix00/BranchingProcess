import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourceOnly.Realization
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourceOnly.ContinuousBoundary
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourceOnly.RealizationContinuousBoundary
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourceOnly.FiniteVariance
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourceOnly.NormalContinuousBoundary

/-!
# Source-only Mogul'skii integration tests

These examples instantiate the final source interfaces directly from the
raw domain-of-attraction assumptions. They cover arbitrary i.i.d.
realizations, the continuous-boundary integral rate, and the centered
unit-variance branch.
-/

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete
open Skorokhod.PathClass.StepCorridor
open scoped ENNReal Topology

noncomputable section

example {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable α μ)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hcenter : α ≠ 1 ∨ IsMogulskiiIndexOneCentered ν normalization)
    {coordinate : ℕ → Ω → ℝ}
    (hindep : iIndepFun coordinate P)
    (hmeasurable : ∀ k, Measurable (coordinate k))
    (hlaw : ∀ k, HasLaw (coordinate k) ν P)
    {G : Set (CadlagPath unitInterval ℝ)}
    (hG : HasRelativeVanishingEnergyGapApproximation α
      Skorokhod.terminalLeftPathSpace G) :
    SourceIidRelativePathClassRate (ν := ν) P α scale coordinate G :=
  sourceIidRelativePathClassRate_of_rawSource P hsmall hStable hDOA hcdf
    hα₀ hα₂ hcenter hindep hmeasurable hlaw hG

example {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {α : ℝ} {scale : ℕ → ℝ} {coordinate : ℕ → Ω → ℝ}
    {G : Set (CadlagPath unitInterval ℝ)}
    (rates : SourceIidRelativePathClassRate (ν := ν) P α scale coordinate G)
    (hnull : ∀ n : ℕ, NullMeasurableSet
      {ω | sourceNormalizedStepCadlagPathIcc scale n
        (fun k => coordinate k ω) ∈ G} P) :=
  rates.probabilityRate hnull

example {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable α μ)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hcenter : α ≠ 1 ∨ IsMogulskiiIndexOneCentered ν normalization)
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    ∃ d Csource : ℝ, 0 < d ∧ Csource < 0 ∧
      (∀ᶠ n : ℕ in atTop,
        0 < ((iidSequenceLaw ν).innerMeasure
          {increment : ℕ → ℝ |
            sourceNormalizedStepCadlagPathIcc scale n increment ∈
              relativeContinuousBoundaryCorridorSet lower upper}).toReal) ∧
      (∀ᶠ n : ℕ in atTop,
        0 < (iidSequenceLaw ν
          {increment : ℕ → ℝ |
            sourceNormalizedStepCadlagPathIcc scale n increment ∈
              relativeContinuousBoundaryCorridorSet lower upper}).toReal) ∧
      Tendsto
        (fun n : ℕ => Real.log
          (((iidSequenceLaw ν).innerMeasure
            {increment : ℕ → ℝ |
              sourceNormalizedStepCadlagPathIcc scale n increment ∈
                relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
              probabilityRateDenominator α ν scale n)
        atTop (𝓝 (rateCoefficient α (d * Csource) *
          ∫ t : unitInterval, continuousBoundaryDensity α lower upper t ∂volume)) ∧
      Tendsto
        (fun n : ℕ => Real.log
          ((iidSequenceLaw ν
            {increment : ℕ → ℝ |
              sourceNormalizedStepCadlagPathIcc scale n increment ∈
                relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
              probabilityRateDenominator α ν scale n)
        atTop (𝓝 (rateCoefficient α (d * Csource) *
          ∫ t : unitInterval, continuousBoundaryDensity α lower upper t ∂volume)) :=
  exists_source_continuousBoundary_inner_outer_rates_of_rawSource
    hsmall hStable hDOA hcdf hα₀ hα₂ hcenter lower upper hwidth hstartLower hstartUpper

example {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable α μ)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hcenter : α ≠ 1 ∨ IsMogulskiiIndexOneCentered ν normalization)
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    ∃ d Csource : ℝ, 0 < d ∧ Csource < 0 ∧
      (∀ᶠ n : ℕ in atTop,
        0 < (iidSequenceLaw ν
          {increment : ℕ → ℝ |
            sourceNormalizedStepCadlagPathIcc scale n increment ∈
              relativeContinuousBoundaryCorridorSet lower upper}).toReal) ∧
      Tendsto
        (fun n : ℕ => Real.log
          ((iidSequenceLaw ν
            {increment : ℕ → ℝ |
              sourceNormalizedStepCadlagPathIcc scale n increment ∈
                relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
              probabilityRateDenominator α ν scale n)
        atTop (𝓝 (rateCoefficient α (d * Csource) *
          ∫ t : unitInterval, continuousBoundaryDensity α lower upper t ∂volume)) :=
  exists_source_continuousBoundary_probability_rate_of_rawSource
    hsmall hStable hDOA hcdf hα₀ hα₂ hcenter lower upper hwidth hstartLower hstartUpper

example {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable α μ)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hcenter : α ≠ 1 ∨ IsMogulskiiIndexOneCentered ν normalization)
    {coordinate : ℕ → Ω → ℝ}
    (hindep : iIndepFun coordinate P)
    (hmeasurable : ∀ k, Measurable (coordinate k))
    (hlaw : ∀ k, HasLaw (coordinate k) ν P)
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    ∃ d Csource : ℝ, 0 < d ∧ Csource < 0 ∧
      (∀ᶠ n : ℕ in atTop,
        0 < (P {ω | sourceNormalizedStepCadlagPathIcc scale n
          (fun k => coordinate k ω) ∈
            relativeContinuousBoundaryCorridorSet lower upper}).toReal) ∧
      Tendsto
        (fun n : ℕ => Real.log
          (P {ω | sourceNormalizedStepCadlagPathIcc scale n
            (fun k => coordinate k ω) ∈
              relativeContinuousBoundaryCorridorSet lower upper}).toReal /
            probabilityRateDenominator α ν scale n)
        atTop (𝓝 (rateCoefficient α (d * Csource) *
          ∫ t : unitInterval, continuousBoundaryDensity α lower upper t ∂volume)) :=
  exists_source_continuousBoundary_probability_rate_of_rawSource_of_iid
    P hsmall hStable hDOA hcdf hα₀ hα₂ hcenter hindep hmeasurable hlaw
      lower upper hwidth hstartLower hstartUpper

example {ν : Measure ℝ} [IsProbabilityMeasure ν] {scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : ∫ x, x ^ 2 ∂ν = 1)
    {G : Set (CadlagPath unitInterval ℝ)}
    (hG : HasRelativeVanishingEnergyGapApproximation 2
      Skorokhod.terminalLeftPathSpace G) :
    HasSourceFiniteVarianceScaledRelativeRate (ν := ν) scale G :=
  sourceScaledInnerOuterLogRate_of_centered_unitVariance
    hsmall hcentered hsquare hvariance hG

example {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable 2 μ)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0)) :
    RawNormalSourceRateData (ν := ν) (μ := μ) scale :=
  rawNormalSourceRateData_of_rawSource hsmall hStable hDOA

example {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable 2 μ)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    {G : Set (CadlagPath unitInterval ℝ)}
    (hG : HasRelativeVanishingEnergyGapApproximation 2
      Skorokhod.terminalLeftPathSpace G) :
    ∃! H : ℝ, HasSourceRelativePathClassRate (ν := ν) 2 scale G
      (rateCoefficient 2 (-(Real.pi ^ 2) / 8)) H :=
  by
    let data := rawNormalSourceRateData_of_rawSource hsmall hStable hDOA
    have hrate := data.relativePathClassRate hG
    simpa [data.normalizedEscape_eq] using hrate

example {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable 2 μ)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    RawNormalContinuousBoundaryRateData (ν := ν) (μ := μ) (scale := scale)
      lower upper :=
  rawNormalContinuousBoundaryRateData_of_rawSource
    hsmall hStable hDOA lower upper hwidth hstartLower hstartUpper

example {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable 2 μ)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    (∀ᶠ n : ℕ in atTop,
      0 < (iidSequenceLaw ν
        {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale n increment ∈
            relativeContinuousBoundaryCorridorSet lower upper}).toReal) ∧
    Tendsto
      (fun n : ℕ => Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ |
            sourceNormalizedStepCadlagPathIcc scale n increment ∈
              relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
            probabilityRateDenominator 2 ν scale n)
      atTop (𝓝 (rateCoefficient 2 (-(Real.pi ^ 2) / 8) *
        ∫ t : unitInterval, continuousBoundaryDensity 2 lower upper t ∂volume)) :=
  rawNormalContinuousBoundaryProbabilityRate_of_rawSource
    hsmall hStable hDOA lower upper hwidth hstartLower hstartUpper

example {ν : Measure ℝ} [IsProbabilityMeasure ν] {scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : ∫ x, x ^ 2 ∂ν = 1)
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    RawNormalContinuousBoundaryRateData (ν := ν) (μ := gaussianReal 0 1)
      (scale := scale) lower upper :=
  rawNormalContinuousBoundaryRateData_of_centered_unitVariance
    hsmall hcentered hsquare hvariance lower upper hwidth hstartLower hstartUpper

example {ν : Measure ℝ} [IsProbabilityMeasure ν] {scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : ∫ x, x ^ 2 ∂ν = 1)
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    (∀ᶠ n : ℕ in atTop,
      0 < (iidSequenceLaw ν
        {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale n increment ∈
            relativeContinuousBoundaryCorridorSet lower upper}).toReal) ∧
    Tendsto
      (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ |
            sourceNormalizedStepCadlagPathIcc scale n increment ∈
              relativeContinuousBoundaryCorridorSet lower upper}).toReal))
      atTop (𝓝 (-(Real.pi ^ 2) / 2 *
        ∫ t : unitInterval, continuousBoundaryDensity 2 lower upper t ∂volume)) :=
  centeredUnitVariance_sourceRelativeContinuousBoundaryProbabilityRate
    hsmall hcentered hsquare hvariance lower upper hwidth hstartLower hstartUpper

example (lower upper : C(unitInterval, ℝ)) (scale : ℕ → ℝ) (n : ℕ) :
    MeasurableSet {increment : ℕ → ℝ |
      sourceNormalizedStepCadlagPathIcc scale n increment ∈
        relativeContinuousBoundaryCorridorSet lower upper} :=
  measurableSet_sourceNormalizedStepCadlagPathIcc_preimage_relativeContinuousBoundaryCorridorSet
    lower upper scale n

#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.exists_source_relative_pathClass_rates_of_rawSource
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.exists_source_continuousBoundary_inner_outer_rates_of_rawSource
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.exists_source_continuousBoundary_probability_rate_of_rawSource
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.exists_source_continuousBoundary_probability_rate_of_rawSource_of_iid
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.sourceIidRelativePathClassRate_of_rawSource
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourceIidRelativePathClassRate.probabilityRate
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.rawNormalSourceRateData_of_rawSource
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.RawNormalSourceRateData.relativePathClassRate
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.rawNormalSourceRateData_of_centered_unitVariance
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.sourceScaledInnerOuterLogRate_of_centered_unitVariance
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HasSourceFiniteVarianceScaledRelativeRate.probabilityRate
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.rawNormalContinuousBoundaryRateData_of_centered_unitVariance
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.rawNormalContinuousBoundaryProbabilityRate_of_rawSource
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredUnitVariance_sourceRelativeContinuousBoundaryProbabilityRate
#print axioms ProbabilityTheory.RandomWalk.sourceNormalizedStepCadlagPathIcc_mem_relativeContinuousBoundaryCorridorSet_iff
#print axioms ProbabilityTheory.RandomWalk.measurableSet_sourceNormalizedStepCadlagPathIcc_preimage_relativeContinuousBoundaryCorridorSet

end

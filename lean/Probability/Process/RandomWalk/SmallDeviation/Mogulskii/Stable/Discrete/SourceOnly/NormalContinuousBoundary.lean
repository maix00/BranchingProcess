/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.ContinuousBoundary
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.ContinuousBoundary
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.Relative
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourceOnly.FiniteVariance
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourceOnly.NormalDomain
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.SourcePathContinuousBoundary

/-!
# Continuous-boundary rates for raw normal-domain sources

The named normal-source rate data lifts to continuous boundary corridors. The
result records the inner and outer rates separately; ordinary probability is
available when the corridor preimages are null-measurable.
-/

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor

/-- Continuous-boundary inner/outer rates together with the source data and
boundary energy they use. -/
structure RawNormalContinuousBoundaryRateData
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {scale : ℕ → ℝ} (lower upper : C(unitInterval, ℝ)) where
  source : RawNormalSourceRateData ν μ scale
  width : ∀ t, lower t < upper t
  startLower : lower ⊥ < 0
  startUpper : 0 < upper ⊥
  innerPositive : ∀ᶠ n : ℕ in atTop,
    0 < ((iidSequenceLaw ν).innerMeasure
      {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
          relativeContinuousBoundaryCorridorSet lower upper}).toReal
  outerPositive : ∀ᶠ n : ℕ in atTop,
    0 < (iidSequenceLaw ν
      {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
          relativeContinuousBoundaryCorridorSet lower upper}).toReal
  innerRate : Tendsto
    (fun n : ℕ => Real.log
      (((iidSequenceLaw ν).innerMeasure
        {increment : ℕ → ℝ |
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
            relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
        probabilityRateDenominator 2 ν scale n)
    atTop (𝓝 (rateCoefficient 2
      (source.timeFactor * source.sourceEscapeConstant) *
        ∫ t : unitInterval, continuousBoundaryDensity 2 lower upper t ∂volume))
  outerRate : Tendsto
    (fun n : ℕ => Real.log
      ((iidSequenceLaw ν
        {increment : ℕ → ℝ |
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
            relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
        probabilityRateDenominator 2 ν scale n)
    atTop (𝓝 (rateCoefficient 2
      (source.timeFactor * source.sourceEscapeConstant) *
        ∫ t : unitInterval, continuousBoundaryDensity 2 lower upper t ∂volume))

/-- A raw normal-source rate record yields inner and outer rates for every
strictly separated continuous corridor whose time-zero interval contains the
origin. -/
noncomputable def RawNormalSourceRateData.continuousBoundaryRates
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {scale : ℕ → ℝ} (source : RawNormalSourceRateData ν μ scale)
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    RawNormalContinuousBoundaryRateData (ν := ν) (μ := μ) (scale := scale)
      lower upper := by
  let paths : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ := fun n increment =>
    RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment
  let denominator : ℕ → ℝ := probabilityRateDenominator 2 ν scale
  let κ : ℝ := rateCoefficient 2
    (source.timeFactor * source.sourceEscapeConstant)
  have hdenom : Tendsto denominator atTop atBot := by
    simpa [denominator] using source.denominator_tendsto_atBot
  have hconstant : source.timeFactor * source.sourceEscapeConstant =
      -(Real.pi ^ 2) / 8 := source.normalizedEscape_eq
  have hdCsource : source.timeFactor * source.sourceEscapeConstant < 0 := by
    rw [hconstant]
    nlinarith [sq_pos_of_pos Real.pi_pos]
  have hκ : 0 < κ := rateCoefficient_pos hdCsource
  have hpaths : ∀ n increment, paths n increment ∈
      Skorokhod.terminalLeftPathSpace := by
    intro n increment
    exact Skorokhod.terminalLeftPath_mem_space
      (RandomWalk.normalizedStepCadlagPathIcc scale n increment)
  have hFiniteUnionRate : ∀ C₃ : FiniteCorridorUnion 2,
      (∀ n : ℕ, NullMeasurableSet
        {increment : ℕ → ℝ | paths n increment ∈ C₃.toSet}
        (iidSequenceLaw ν)) ∧
      (∀ᶠ n : ℕ in atTop,
        0 < (iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ C₃.toSet}).toReal) ∧
      Tendsto (fun n : ℕ => Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ C₃.toSet}).toReal) /
            denominator n)
        atTop (𝓝 (κ * C₃.realEnergy)) := by
    intro C₃
    simpa [paths, denominator, κ] using source.finiteCorridorUnionRate C₃
  obtain ⟨hInnerPos, hOuterPos, hInnerRate, hOuterRate⟩ :=
    ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability.tendsto_inner_outer_log_probability_ratio_of_finiteCorridorUnionRates_continuousBoundary
      (iidSequenceLaw ν) paths denominator hdenom hκ hpaths hFiniteUnionRate
      lower upper hwidth hstartLower hstartUpper
  exact {
    source := source
    width := hwidth
    startLower := hstartLower
    startUpper := hstartUpper
    innerPositive := by simpa [paths] using hInnerPos
    outerPositive := by simpa [paths] using hOuterPos
    innerRate := by simpa [paths, denominator, κ] using hInnerRate
    outerRate := by simpa [paths, denominator, κ] using hOuterRate
  }

/-- Direct continuous-boundary rate data from the raw normal-domain
assumptions. -/
noncomputable def rawNormalContinuousBoundaryRateData_of_rawSource
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable 2 μ)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    RawNormalContinuousBoundaryRateData (ν := ν) (μ := μ) (scale := scale)
      lower upper :=
  (rawNormalSourceRateData_of_rawSource hsmall hStable hDOA).continuousBoundaryRates
    lower upper hwidth hstartLower hstartUpper

/-- Theorem 3's centered, unit-variance assumptions give the continuous
boundary rates directly, through the existing normal-domain theorem. -/
noncomputable def rawNormalContinuousBoundaryRateData_of_centered_unitVariance
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : ∫ x, x ^ 2 ∂ν = 1)
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    RawNormalContinuousBoundaryRateData (ν := ν) (μ := gaussianReal 0 1)
      (scale := scale) lower upper :=
  (rawNormalSourceRateData_of_centered_unitVariance
    hsmall hcentered hsquare hvariance).continuousBoundaryRates
      lower upper hwidth hstartLower hstartUpper

/-- Null-measurability identifies the inner and outer limits with ordinary
probability. -/
theorem RawNormalContinuousBoundaryRateData.probabilityRate
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {scale : ℕ → ℝ} {lower upper : C(unitInterval, ℝ)}
    (rates : RawNormalContinuousBoundaryRateData (ν := ν) (μ := μ)
      (scale := scale) lower upper) :
    (∀ᶠ n : ℕ in atTop,
      0 < (iidSequenceLaw ν
        {increment : ℕ → ℝ |
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
            relativeContinuousBoundaryCorridorSet lower upper}).toReal) ∧
    Tendsto
      (fun n : ℕ => Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
              relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
            probabilityRateDenominator 2 ν scale n)
      atTop (𝓝 (rateCoefficient 2
        (rates.source.timeFactor * rates.source.sourceEscapeConstant) *
          ∫ t : unitInterval, continuousBoundaryDensity 2 lower upper t ∂volume)) := by
  let paths : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ := fun n increment =>
    RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment
  let denominator : ℕ → ℝ := probabilityRateDenominator 2 ν scale
  let κ : ℝ := rateCoefficient 2
    (rates.source.timeFactor * rates.source.sourceEscapeConstant)
  have hdenom : Tendsto denominator atTop atBot := by
    simpa [denominator] using rates.source.denominator_tendsto_atBot
  have hconstant : rates.source.timeFactor * rates.source.sourceEscapeConstant =
      -(Real.pi ^ 2) / 8 := rates.source.normalizedEscape_eq
  have hdCsource : rates.source.timeFactor * rates.source.sourceEscapeConstant < 0 := by
    rw [hconstant]
    nlinarith [sq_pos_of_pos Real.pi_pos]
  have hκ : 0 < κ := rateCoefficient_pos hdCsource
  have hpaths : ∀ n increment, paths n increment ∈
      Skorokhod.terminalLeftPathSpace := by
    intro n increment
    exact Skorokhod.terminalLeftPath_mem_space
      (RandomWalk.normalizedStepCadlagPathIcc scale n increment)
  have hFiniteUnionRate : ∀ C₃ : FiniteCorridorUnion 2,
      (∀ n : ℕ, NullMeasurableSet
        {increment : ℕ → ℝ | paths n increment ∈ C₃.toSet}
        (iidSequenceLaw ν)) ∧
      (∀ᶠ n : ℕ in atTop,
        0 < (iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ C₃.toSet}).toReal) ∧
      Tendsto (fun n : ℕ => Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ C₃.toSet}).toReal) /
            denominator n)
        atTop (𝓝 (κ * C₃.realEnergy)) := by
    intro C₃
    simpa [paths, denominator, κ] using rates.source.finiteCorridorUnionRate C₃
  have hnull : ∀ n : ℕ, NullMeasurableSet
      {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
          relativeContinuousBoundaryCorridorSet lower upper}
      (iidSequenceLaw ν) := by
    intro n
    exact (RandomWalk.measurableSet_sourceNormalizedStepCadlagPathIcc_preimage_relativeContinuousBoundaryCorridorSet
      lower upper scale n).nullMeasurableSet
  have hprobability :=
    ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability.tendsto_log_probability_ratio_of_finiteCorridorUnionRates_continuousBoundary
      (iidSequenceLaw ν) paths denominator hdenom hκ hpaths hFiniteUnionRate
      lower upper rates.width rates.startLower rates.startUpper hnull
  exact hprobability

/-- Raw normal-domain assumptions give the ordinary source-endpoint
probability rate for a strictly separated continuous corridor. The rate is
expressed using the negative denominator
`-n * L*(scale n) / scale n²`; its normalized escape constant is the
universal Gaussian value `-π²/8`, with no Brownian-process witness or moment
premise. -/
theorem rawNormalContinuousBoundaryProbabilityRate_of_rawSource
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
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
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
            relativeContinuousBoundaryCorridorSet lower upper}).toReal) ∧
    Tendsto
      (fun n : ℕ => Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
              relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
            probabilityRateDenominator 2 ν scale n)
      atTop (𝓝 (rateCoefficient 2 (-(Real.pi ^ 2) / 8) *
        ∫ t : unitInterval, continuousBoundaryDensity 2 lower upper t ∂volume)) := by
  let rates := rawNormalContinuousBoundaryRateData_of_rawSource
    hsmall hStable hDOA lower upper hwidth hstartLower hstartUpper
  have hrate := rates.probabilityRate
  have hcoefficient : rateCoefficient 2
      (rates.source.timeFactor * rates.source.sourceEscapeConstant) =
        rateCoefficient 2 (-(Real.pi ^ 2) / 8) :=
    congrArg (rateCoefficient 2) rates.source.normalizedEscape_eq
  rw [hcoefficient] at hrate
  exact hrate

/-- The centered, unit-variance continuous-boundary case of Mogul'skii's
Theorem 3, in the paper's `scale² / n` normalization. The source-path event
is measurable by its finite-step cell characterization. -/
theorem centeredUnitVariance_sourceRelativeContinuousBoundaryProbabilityRate
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {scale : ℕ → ℝ}
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
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
            relativeContinuousBoundaryCorridorSet lower upper}).toReal) ∧
    Tendsto
      (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
              relativeContinuousBoundaryCorridorSet lower upper}).toReal))
      atTop (𝓝 (-(Real.pi ^ 2) / 2 *
        ∫ t : unitInterval, continuousBoundaryDensity 2 lower upper t ∂volume)) := by
  let G := relativeContinuousBoundaryCorridorSet lower upper
  have hG : HasRelativeVanishingEnergyGapApproximation 2
      Skorokhod.terminalLeftPathSpace G := by
    simpa [G] using continuousBoundary_hasRelativeVanishingEnergyGapApproximation
      2 lower upper hwidth hstartLower hstartUpper
  let rates : HasSourceFiniteVarianceScaledRelativeRate (ν := ν) scale G :=
    sourceScaledInnerOuterLogRate_of_centered_unitVariance
      hsmall hcentered hsquare hvariance hG
  have hnull : ∀ n : ℕ, NullMeasurableSet
      {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
          relativeContinuousBoundaryCorridorSet lower upper}
      (iidSequenceLaw ν) := by
    intro n
    exact (RandomWalk.measurableSet_sourceNormalizedStepCadlagPathIcc_preimage_relativeContinuousBoundaryCorridorSet
      lower upper scale n).nullMeasurableSet
  have hprobability := rates.probabilityRate (by simpa [G] using hnull)
  have henergy : rates.energy =
      ∫ t : unitInterval, continuousBoundaryDensity 2 lower upper t ∂volume := by
    let source := rawNormalSourceRateData_of_centered_unitVariance
      hsmall hcentered hsquare hvariance
    let paths : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ := fun n increment =>
      RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment
    let denominator : ℕ → ℝ := probabilityRateDenominator 2 ν scale
    have hpaths : ∀ n increment, paths n increment ∈
        Skorokhod.terminalLeftPathSpace := by
      intro n increment
      exact Skorokhod.terminalLeftPath_mem_space
        (RandomWalk.normalizedStepCadlagPathIcc scale n increment)
    have hnegative : source.timeFactor * source.sourceEscapeConstant < 0 := by
      rw [source.normalizedEscape_eq]
      nlinarith [sq_pos_of_pos Real.pi_pos]
    have hκ : 0 < rateCoefficient 2
        (source.timeFactor * source.sourceEscapeConstant) :=
      rateCoefficient_pos hnegative
    have hFiniteUnionRate : ∀ C₃ : FiniteCorridorUnion 2,
        (∀ n : ℕ, NullMeasurableSet
          {increment : ℕ → ℝ | paths n increment ∈ C₃.toSet}
          (iidSequenceLaw ν)) ∧
        (∀ᶠ n : ℕ in atTop,
          0 < (iidSequenceLaw ν
            {increment : ℕ → ℝ | paths n increment ∈ C₃.toSet}).toReal) ∧
        Tendsto (fun n : ℕ => Real.log
          ((iidSequenceLaw ν
            {increment : ℕ → ℝ | paths n increment ∈ C₃.toSet}).toReal) /
              denominator n)
          atTop (𝓝 (rateCoefficient 2
            (source.timeFactor * source.sourceEscapeConstant) * C₃.realEnergy)) := by
      intro C₃
      simpa [paths, denominator] using source.finiteCorridorUnionRate C₃
    obtain ⟨otherApproximation, otherLimits, hOtherEnergy⟩ :=
      exists_continuousBoundary_relativeApproximation_commonEnergy_eq_integral
        2 lower upper hwidth hstartLower hstartUpper
    have hcommonEnergy :=
      RelativeFiniteCorridorUnionEnergyLimits.commonEnergy_eq_of_approximation
        (iidSequenceLaw ν) paths Skorokhod.terminalLeftPathSpace hpaths denominator
        source.denominator_tendsto_atBot hκ rates.approximation otherApproximation
        rates.energyLimits otherLimits hFiniteUnionRate
    exact rates.energy_eq.trans (hcommonEnergy.trans hOtherEnergy)
  refine ⟨hprobability.1, ?_⟩
  simpa [henergy, G] using hprobability.2

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

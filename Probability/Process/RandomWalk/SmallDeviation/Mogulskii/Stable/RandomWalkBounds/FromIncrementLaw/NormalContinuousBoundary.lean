/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.ContinuousBoundary
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.ContinuousBoundary
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.Relative
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.FiniteVariance
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.NormalDomain
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

/-- The centered finite-variance continuous-boundary case of Mogul'skii's
Theorem 3, in the paper's `scale² / n` normalization. The variance enters
through the truncated-second-moment limit; the increment law is not
standardized. The standard-Gaussian domain-of-attraction input uses the
norming sequence `sqrt (n * variance)`, while the source-path event still uses
the original increments and the given `scale`. The source-path event is
measurable by its finite-step cell characterization. -/
theorem centeredFiniteVariance_sourceRelativeContinuousBoundaryProbabilityRate
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
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
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν) *
        ∫ t : unitInterval, continuousBoundaryDensity 2 lower upper t ∂volume)) := by
  let G := relativeContinuousBoundaryCorridorSet lower upper
  let variance : ℝ := ∫ x, x ^ 2 ∂ν
  let normalization : ℕ → ℝ := fun n => Real.sqrt ((n : ℝ) * variance)
  let sigma : ℝ := Real.sqrt variance
  have hvariance' : 0 < variance := by
    simpa [variance] using hvariance
  have hsigma : 0 < sigma := Real.sqrt_pos.2 hvariance'
  have hDOA :=
    isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_integrable_sq
      ν hcentered hsquare hvariance
  have hnormalizationRatio : Tendsto
      (fun n : ℕ => normalization n / Real.sqrt (n : ℝ)) atTop
        (𝓝 sigma) := by
    have heq : (fun n : ℕ => normalization n / Real.sqrt (n : ℝ)) =ᶠ[atTop]
        fun _ => sigma := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
      have hsqrt : Real.sqrt ((n : ℝ) * variance) =
          Real.sqrt (n : ℝ) * Real.sqrt variance :=
        Real.sqrt_mul (Nat.cast_nonneg n) variance
      have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
      rw [show normalization n = Real.sqrt ((n : ℝ) * variance) by rfl,
        hsqrt, show sigma = Real.sqrt variance by rfl]
      field_simp [ne_of_gt hsqrtPos]
    exact tendsto_const_nhds.congr' heq.symm
  have hrootPos : ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsmall' : Asymptotics.IsSmallDeviationScale scale normalization :=
    hsmall.of_tendsto_normalization_ratio hrootPos hnormalizationRatio hsigma
  have hstable : IsStrictlyAlphaStable 2 (gaussianReal 0 1) :=
    isStrictlyAlphaStable_gaussianReal_zero (v := 1) (by norm_num)
  let source := rawNormalSourceRateData_of_rawSource hsmall' hstable hDOA
  let rates := source.continuousBoundaryRates lower upper hwidth hstartLower hstartUpper
  have hrawProbability := rates.probabilityRate
  have hcoefficient : rateCoefficient 2
      (rates.source.timeFactor * rates.source.sourceEscapeConstant) =
        rateCoefficient 2 (-(Real.pi ^ 2) / 8) :=
    congrArg (rateCoefficient 2) rates.source.normalizedEscape_eq
  rw [hcoefficient] at hrawProbability
  have htruncated := tendsto_truncatedSecondMoment ν hsquare
  have hvarianceLimit : Tendsto
      (fun n : ℕ => truncatedSecondMoment ν (scale n)) atTop
        (𝓝 (∫ x, x ^ 2 ∂ν)) := by
    simpa only [Function.comp_def] using htruncated.comp hsmall.tendsto_atTop
  have hvariancePositive : ∀ᶠ n : ℕ in atTop,
      0 < truncatedSecondMoment ν (scale n) :=
    hvarianceLimit.eventually (Ioi_mem_nhds hvariance)
  have hscaledRate : Tendsto
      (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
              relativeContinuousBoundaryCorridorSet lower upper}).toReal))
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν) *
        ∫ t : unitInterval, continuousBoundaryDensity 2 lower upper t ∂volume)) := by
    have hproduct := hrawProbability.2.mul hvarianceLimit.neg
    have hcoefficient' : rateCoefficient 2 (-(Real.pi ^ 2) / 8) =
        (Real.pi ^ 2) / 2 := by
      rw [rateCoefficient]
      norm_num [Real.rpow_natCast]
      ring
    have hlimit : rateCoefficient 2 (-(Real.pi ^ 2) / 8) *
        (∫ t : unitInterval, continuousBoundaryDensity 2 lower upper t ∂volume) *
          (-(∫ x, x ^ 2 ∂ν)) =
        -(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν) *
          ∫ t : unitInterval, continuousBoundaryDensity 2 lower upper t ∂volume := by
      rw [hcoefficient']
      ring
    have hEq : (fun n : ℕ => Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
              relativeContinuousBoundaryCorridorSet lower upper}).toReal) /
          probabilityRateDenominator 2 ν scale n *
            (-(truncatedSecondMoment ν (scale n)))) =ᶠ[atTop]
        (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
          ((iidSequenceLaw ν
            {increment : ℕ → ℝ |
              RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
                relativeContinuousBoundaryCorridorSet lower upper}).toReal)) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ), hsmall.eventually_pos,
        hvariancePositive] with n hn hscale hmoment
      have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hscaleNe : scale n ≠ 0 := ne_of_gt hscale
      have hmomentNe : truncatedSecondMoment ν (scale n) ≠ 0 := ne_of_gt hmoment
      rw [probabilityRateDenominator, stableSmallDeviationRate_two]
      field_simp [hnReal, hscaleNe, hmomentNe]
    have hlimit' := hproduct.congr' hEq
    simpa [hlimit] using hlimit'
  exact ⟨hrawProbability.1, by simpa [G] using hscaledRate⟩

/-- A finite union of admissible step corridors has its finite-variance
source-path rate in the `scale² / n` normalization. This form is useful when
the corridor itself has a terminal jump: changing the boundary at `t = 1`
does not require approximating it by continuous boundaries. -/
theorem centeredFiniteVariance_sourceFiniteCorridorUnionProbabilityRate
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
    (C₃ : FiniteCorridorUnion 2) :
    (∀ᶠ n : ℕ in atTop,
      0 < (iidSequenceLaw ν
        {increment : ℕ → ℝ |
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ C₃.toSet}).toReal) ∧
    Tendsto
      (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ C₃.toSet}).toReal))
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν) * C₃.realEnergy)) := by
  let variance : ℝ := ∫ x, x ^ 2 ∂ν
  let normalization : ℕ → ℝ := fun n => Real.sqrt ((n : ℝ) * variance)
  let sigma : ℝ := Real.sqrt variance
  have hvariance' : 0 < variance := by simpa [variance] using hvariance
  have hsigma : 0 < sigma := Real.sqrt_pos.2 hvariance'
  have hDOA :=
    isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_integrable_sq
      ν hcentered hsquare hvariance
  have hnormalizationRatio : Tendsto
      (fun n : ℕ => normalization n / Real.sqrt (n : ℝ)) atTop (𝓝 sigma) := by
    have heq : (fun n : ℕ => normalization n / Real.sqrt (n : ℝ)) =ᶠ[atTop]
        fun _ => sigma := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
      have hsqrt : Real.sqrt ((n : ℝ) * variance) =
          Real.sqrt (n : ℝ) * Real.sqrt variance :=
        Real.sqrt_mul (Nat.cast_nonneg n) variance
      have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
      rw [show normalization n = Real.sqrt ((n : ℝ) * variance) by rfl,
        hsqrt, show sigma = Real.sqrt variance by rfl]
      field_simp [ne_of_gt hsqrtPos]
    exact tendsto_const_nhds.congr' heq.symm
  have hrootPos : ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsmall' : Asymptotics.IsSmallDeviationScale scale normalization :=
    hsmall.of_tendsto_normalization_ratio hrootPos hnormalizationRatio hsigma
  have hstable : IsStrictlyAlphaStable 2 (gaussianReal 0 1) :=
    isStrictlyAlphaStable_gaussianReal_zero (v := 1) (by norm_num)
  let source := rawNormalSourceRateData_of_rawSource hsmall' hstable hDOA
  have hraw := source.finiteCorridorUnionRate C₃
  have htruncated := tendsto_truncatedSecondMoment ν hsquare
  have hvarianceLimit : Tendsto
      (fun n : ℕ => truncatedSecondMoment ν (scale n)) atTop (𝓝 variance) := by
    simpa only [Function.comp_def] using htruncated.comp hsmall.tendsto_atTop
  have hvariancePositive : ∀ᶠ n : ℕ in atTop,
      0 < truncatedSecondMoment ν (scale n) :=
    hvarianceLimit.eventually (Ioi_mem_nhds hvariance')
  have hcoefficient : rateCoefficient 2 (-(Real.pi ^ 2) / 8) = (Real.pi ^ 2) / 2 := by
    rw [rateCoefficient]
    norm_num [Real.rpow_natCast]
    ring
  have hscaledRate : Tendsto
      (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ C₃.toSet}).toReal))
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * variance * C₃.realEnergy)) := by
    have hrawLimit : Tendsto
        (fun n : ℕ => Real.log
          ((iidSequenceLaw ν
            {increment : ℕ → ℝ |
              RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ C₃.toSet}).toReal) /
            probabilityRateDenominator 2 ν scale n)
        atTop (𝓝 ((Real.pi ^ 2) / 2 * C₃.realEnergy)) := by
      have hnormalized := hraw.2.2
      have hescape : source.timeFactor * source.sourceEscapeConstant =
          -(Real.pi ^ 2) / 8 := source.normalizedEscape_eq
      rw [hescape] at hnormalized
      simpa [hcoefficient] using hnormalized
    have hproduct := hrawLimit.mul hvarianceLimit.neg
    have hEq : (fun n : ℕ => Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ C₃.toSet}).toReal) /
          probabilityRateDenominator 2 ν scale n *
            (-(truncatedSecondMoment ν (scale n)))) =ᶠ[atTop]
        (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
          ((iidSequenceLaw ν
            {increment : ℕ → ℝ |
              RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ C₃.toSet}).toReal)) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ), hsmall.eventually_pos,
        hvariancePositive] with n hn hscale hmoment
      have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hscaleNe : scale n ≠ 0 := ne_of_gt hscale
      have hmomentNe : truncatedSecondMoment ν (scale n) ≠ 0 := ne_of_gt hmoment
      rw [probabilityRateDenominator, stableSmallDeviationRate_two]
      field_simp [hnReal, hscaleNe, hmomentNe]
    have hlimit : (Real.pi ^ 2) / 2 * C₃.realEnergy * (-variance) =
        -(Real.pi ^ 2) / 2 * variance * C₃.realEnergy := by ring
    simpa [hlimit] using hproduct.congr' hEq
  exact ⟨hraw.2.1, hscaledRate⟩

/-- The unit-variance continuous-boundary rate is the finite-variance result
specialized to second moment one. -/
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
  have hvariancePos : 0 < ∫ x : ℝ, x ^ 2 ∂ν := by
    rw [hvariance]
    norm_num
  simpa [hvariance] using
    centeredFiniteVariance_sourceRelativeContinuousBoundaryProbabilityRate
      hsmall hcentered hsquare hvariancePos lower upper hwidth hstartLower hstartUpper

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

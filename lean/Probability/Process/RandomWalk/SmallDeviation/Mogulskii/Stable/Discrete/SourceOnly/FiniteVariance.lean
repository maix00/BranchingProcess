/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Moments.Truncated
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourceOnly.NormalDomain

/-!
# Finite-variance source rates

The finite-variance normal-domain branch is stated for relative path classes,
independently of the continuous-boundary specialization. Its ordinary
probability form identifies the inner measure with the event measure under an
explicit null-measurability hypothesis.
-/

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor

/-- The centered finite-variance unit-variance specialization has the exact
standard-normal rate coefficient in the paper's normalization. -/
theorem centeredUnitVariance_sourceRelativePathClassRate
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : ∫ x, x ^ 2 ∂ν = 1)
    {G : Set (CadlagPath unitInterval ℝ)}
    (hG : HasRelativeVanishingEnergyGapApproximation 2
      Skorokhod.terminalLeftPathSpace G) :
    ∃! H : ℝ, HasSourceRelativePathClassRate (ν := ν) 2 scale G
      (rateCoefficient 2 (-(Real.pi ^ 2) / 8)) H := by
  let source := rawNormalSourceRateData_of_centered_unitVariance
    hsmall hcentered hsquare hvariance
  simpa [source, RawNormalSourceRateData.normalizedEscape_eq] using
    source.relativePathClassRate hG

/-- Theorem 3's relative path-class conclusion in its displayed
`scale² / n` normalization. Named fields expose the common energy and the
inner and outer limits without requiring measurability of `G`. -/
structure HasSourceFiniteVarianceScaledRelativeRate
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (scale : ℕ → ℝ)
    (G : Set (CadlagPath unitInterval ℝ)) where
  energy : ℝ
  approximation : RelativeFiniteCorridorUnionApproximation 2
    Skorokhod.terminalLeftPathSpace G
  energyLimits : RelativeFiniteCorridorUnionEnergyLimits approximation
  energy_eq : energy = energyLimits.commonEnergy
  innerPositive : ∀ᶠ n : ℕ in atTop,
    0 < ((iidSequenceLaw ν).innerMeasure
      {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal
  outerPositive : ∀ᶠ n : ℕ in atTop,
    0 < (iidSequenceLaw ν
      {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal
  innerRate : Tendsto
    (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
      (((iidSequenceLaw ν).innerMeasure
        {increment : ℕ → ℝ |
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal))
    atTop (𝓝 (-(Real.pi ^ 2) / 2 * energy))
  outerRate : Tendsto
    (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
      ((iidSequenceLaw ν
        {increment : ℕ → ℝ |
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal))
    atTop (𝓝 (-(Real.pi ^ 2) / 2 * energy))

/-- Centered unit-variance increments prove the finite-variance normal-domain
rate for every relative `D₀` path class, without an external Brownian witness
or a measurable-target assumption. -/
noncomputable def sourceScaledInnerOuterLogRate_of_centered_unitVariance
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : ∫ x, x ^ 2 ∂ν = 1)
    {G : Set (CadlagPath unitInterval ℝ)}
    (hG : HasRelativeVanishingEnergyGapApproximation 2
      Skorokhod.terminalLeftPathSpace G) :
    HasSourceFiniteVarianceScaledRelativeRate (ν := ν) scale G := by
  let source := rawNormalSourceRateData_of_centered_unitVariance
    hsmall hcentered hsquare hvariance
  have hslowMoment := (tendsto_truncatedSecondMoment ν hsquare).comp
    source.scale_tendsto_atTop
  have hslow : Tendsto (fun n : ℕ => stableSlowVariation 2 ν (scale n))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, stableSlowVariation_two, hvariance] using hslowMoment
  have hslowPos : ∀ᶠ n : ℕ in atTop,
      0 < stableSlowVariation 2 ν (scale n) :=
    hslow.eventually (Ioi_mem_nhds (by norm_num))
  have hratePos : ∀ᶠ n : ℕ in atTop,
      0 < stableSmallDeviationRate 2 ν scale n := by
    have hdenomNeg : ∀ᶠ n : ℕ in atTop,
        probabilityRateDenominator 2 ν scale n < 0 :=
      source.denominator_tendsto_atBot.eventually
        (eventually_lt_atBot (0 : ℝ))
    filter_upwards [hdenomNeg] with n hn
    rw [probabilityRateDenominator] at hn
    have hinv : 0 < (stableSmallDeviationRate 2 ν scale n)⁻¹ := by linarith
    exact inv_pos.mp hinv
  have hsourceUnique := source.relativePathClassRate hG
  have hsourceUnique' : ∃! H : ℝ,
      HasSourceRelativePathClassRate (ν := ν) 2 scale G
        (rateCoefficient 2 (-(Real.pi ^ 2) / 8)) H := by
    simpa [source.normalizedEscape_eq] using hsourceUnique
  let H : ℝ := Classical.choose hsourceUnique'
  have hsourceRate : HasSourceRelativePathClassRate (ν := ν) 2 scale G
      (rateCoefficient 2 (-(Real.pi ^ 2) / 8)) H :=
    (Classical.choose_spec hsourceUnique').1
  let A : RelativeFiniteCorridorUnionApproximation 2
      Skorokhod.terminalLeftPathSpace G := Classical.choose hsourceRate
  have hA := Classical.choose_spec hsourceRate
  let hLimits : RelativeFiniteCorridorUnionEnergyLimits A := Classical.choose hA
  have hPieces := Classical.choose_spec hA
  rcases hPieces with ⟨hEnergyEq, hInnerPos, hOuterPos, hInnerRate, hOuterRate⟩
  have hcoefficient :
      -(rateCoefficient 2 (-(Real.pi ^ 2) / 8) * H) =
        -(Real.pi ^ 2) / 2 * H := by
    have hpow : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num [Real.rpow_natCast]
    rw [rateCoefficient, hpow]
    ring
  have hInnerStable : Tendsto
      (fun n : ℕ => Real.log
        (((iidSequenceLaw ν).innerMeasure
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
          stableRateNormalization 2 ν scale n)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * H)) := by
    have h := tendsto_log_div_stableRateNormalization_of_neg hratePos hInnerRate
    simpa [hcoefficient] using h
  have hOuterStable : Tendsto
      (fun n : ℕ => Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
          stableRateNormalization 2 ν scale n)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * H)) := by
    have h := tendsto_log_div_stableRateNormalization_of_neg hratePos hOuterRate
    simpa [hcoefficient] using h
  have hInnerScaled : Tendsto
      (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
        (((iidSequenceLaw ν).innerMeasure
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal))
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * H)) := by
    have hproduct := hInnerStable.mul hslow
    have hEq : (fun n : ℕ =>
        (Real.log (((iidSequenceLaw ν).innerMeasure
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
          stableRateNormalization 2 ν scale n) * stableSlowVariation 2 ν (scale n)) =ᶠ[atTop]
        fun n => (scale n) ^ 2 / (n : ℝ) * Real.log
          (((iidSequenceLaw ν).innerMeasure
            {increment : ℕ → ℝ |
              RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ), hsmall.eventually_pos, hslowPos]
        with n hn hscalePos hmomentPos
      rw [stableRateNormalization_eq, stableSlowVariation_two]
      have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hmomentNe : truncatedSecondMoment ν (scale n) ≠ 0 := by
        have hmomentPos' : 0 < truncatedSecondMoment ν (scale n) := by
          simpa only [stableSlowVariation_two] using hmomentPos
        exact ne_of_gt hmomentPos'
      rw [Real.rpow_two]
      field_simp [hnReal, hmomentNe]
    have hfinal := hproduct.congr' hEq
    convert hfinal using 1 <;> ring_nf
  have hOuterScaled : Tendsto
      (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal))
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * H)) := by
    have hproduct := hOuterStable.mul hslow
    have hEq : (fun n : ℕ =>
        (Real.log ((iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
          stableRateNormalization 2 ν scale n) * stableSlowVariation 2 ν (scale n)) =ᶠ[atTop]
        fun n => (scale n) ^ 2 / (n : ℝ) * Real.log
          ((iidSequenceLaw ν
            {increment : ℕ → ℝ |
              RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ), hsmall.eventually_pos, hslowPos]
        with n hn hscalePos hmomentPos
      rw [stableRateNormalization_eq, stableSlowVariation_two]
      have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hmomentNe : truncatedSecondMoment ν (scale n) ≠ 0 := by
        have hmomentPos' : 0 < truncatedSecondMoment ν (scale n) := by
          simpa only [stableSlowVariation_two] using hmomentPos
        exact ne_of_gt hmomentPos'
      rw [Real.rpow_two]
      field_simp [hnReal, hmomentNe]
    have hfinal := hproduct.congr' hEq
    convert hfinal using 1 <;> ring_nf
  exact {
    energy := H
    approximation := A
    energyLimits := hLimits
    energy_eq := hEnergyEq
    innerPositive := hInnerPos
    outerPositive := hOuterPos
    innerRate := hInnerScaled
    outerRate := hOuterScaled }

/-- Null-measurability turns the source theorem's inner-measure limit into
an ordinary probability limit. -/
theorem HasSourceFiniteVarianceScaledRelativeRate.probabilityRate
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {scale : ℕ → ℝ}
    {G : Set (CadlagPath unitInterval ℝ)}
    (rates : HasSourceFiniteVarianceScaledRelativeRate (ν := ν) scale G)
    (hnull : ∀ n : ℕ, NullMeasurableSet
      {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}
      (iidSequenceLaw ν)) :
    (∀ᶠ n : ℕ in atTop,
      0 < (iidSequenceLaw ν
        {increment : ℕ → ℝ |
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
    Tendsto
      (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal))
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * rates.energy)) := by
  let P := iidSequenceLaw ν
  have hmeasureEq : ∀ n : ℕ,
      P.innerMeasure
        {increment : ℕ → ℝ |
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G} =
      P {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G} := by
    intro n
    exact innerMeasure_eq_measure_of_nullMeasurableSet P (hnull n)
  have hprobPos : ∀ᶠ n : ℕ in atTop,
      0 < (P
        {increment : ℕ → ℝ |
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal := by
    filter_upwards [rates.innerPositive] with n hn
    simpa [P, hmeasureEq n] using hn
  have hprobRate : Tendsto
      (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
        (P {increment : ℕ → ℝ |
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * rates.energy)) := by
    have heq : (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
        (P {increment : ℕ → ℝ |
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) =
        fun n => (scale n) ^ 2 / (n : ℝ) * Real.log
          (P.innerMeasure
            {increment : ℕ → ℝ |
              RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal := by
      funext n
      rw [← hmeasureEq n]
    rw [heq]
    exact rates.innerRate
  exact ⟨hprobPos, hprobRate⟩
end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

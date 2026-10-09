/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PathClassRate
import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLimit.Source
import Probability.Process.RandomWalk.FunctionalLimit.Stable.Centering
import Probability.Distributions.Stable.Attraction.NormingRatios.Tauberian
import Probability.Process.RandomWalk.FunctionalLimit.Normal.Tightness
import Probability.Distributions.Gaussian.Interval
import Probability.Process.Stable.Brownian.PathLaw

/-!
# Stable-domain hypotheses for the path-class Mogul'skii theorem

This file derives the slowly varying factor, stable-process escape rate, and
random-walk tightness from the usual stable-domain assumptions in the three
non-Gaussian regimes.  This makes those analytic inputs consequences of the
theorem hypotheses instead of opaque premises of the discrete estimate.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

/-- Main stable-domain path-class theorem, with tightness and the slowly
varying factor supplied as explicit inputs.  The exact target-set event is
measurable because `G` is Borel and every finite-step path map is measurable.
-/
theorem tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_stableInputs
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {XΩ : Type*} [MeasurableSpace XΩ]
    {X : ℝ≥0 → XΩ → ℝ} {Q : Measure XΩ} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G)
    (hGmeas : MeasurableSet G) :
    ∃ C, HasStableProcessEscapeRate α μ
      (hX.unitIntervalPathLaw : Measure (CadlagPath unitInterval ℝ)) C ∧
      (∀ n : ℕ,
        NullMeasurableSet
          {increment : ℕ → ℝ |
            RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}
          (iidSequenceLaw ν)) ∧
      ∃! H : ℝ,
        (∃ A : FiniteCorridorUnionApproximation α G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
          H = hLimits.commonEnergy) ∧
        Tendsto
          (fun n : ℕ => Real.log
            ((iidSequenceLaw ν {increment : ℕ → ℝ |
              RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
              stableRateNormalization α ν scale n)
          atTop (𝓝 (C * 2 ^ α * H)) := by
  obtain ⟨C, hEscape⟩ :=
    hX.isStableClockProcessLaw_unitIntervalPathLaw
      |>.hasStableProcessEscapeRate_of_isStableLevyProcess hX hcdf
  have hGnull : ∀ n : ℕ,
      NullMeasurableSet
        {increment : ℕ → ℝ |
          RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}
        (iidSequenceLaw ν) := by
    intro n
    have hpath : Measurable (RandomWalk.normalizedStepCadlagPathIcc scale n) :=
      RandomWalk.measurable_normalizedStepCadlagPathIcc scale n
    exact (hGmeas.preimage hpath).nullMeasurableSet
  have hresult := tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_discretestepCorridorRates
    hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase hG hGnull
  rcases hresult.2 with ⟨H, hH, hUnique⟩
  have hratePos := stableSmallDeviationRate_pos_eventually hscale hslow
  have hsource := tendsto_log_div_stableRateNormalization_of_neg hratePos hH.2
  have hcoef : -(rateCoefficient α C * H) =
      C * 2 ^ α * H := by
    dsimp [rateCoefficient]
    ring
  refine ⟨C, hEscape, hresult.1, H, ⟨hH.1, ?_⟩, ?_⟩
  · simpa [hcoef] using hsource
  · intro H' hH'
    apply hUnique H'
    refine ⟨hH'.1, ?_⟩
    have hnegative :=
      tendsto_log_div_probabilityRateDenominator_of_stableRateNormalization
        hratePos hH'.2
    have hcoef' : -(C * 2 ^ α * H') = rateCoefficient α C * H' := by
      dsimp [rateCoefficient]
      ring
    simpa [hcoef'] using hnegative

/-- Stable-domain Mogul'skii theorem below index one.  Regular variation of
the tails gives the J₁ tightness criterion; the stable-domain Tauberian result
gives the slowly varying factor used in the small-deviation normalization.
-/
theorem tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_index_lt_one
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    {XΩ : Type*} [MeasurableSpace XΩ]
    {X : ℝ≥0 → XΩ → ℝ} {Q : Measure XΩ} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G)
    (hGmeas : MeasurableSet G) :
    ∃ C, HasStableProcessEscapeRate α μ
      (hX.unitIntervalPathLaw : Measure (CadlagPath unitInterval ℝ)) C ∧
      (∀ n : ℕ,
        NullMeasurableSet
          {increment : ℕ → ℝ |
            RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}
          (iidSequenceLaw ν)) ∧
      ∃! H : ℝ,
        (∃ A : FiniteCorridorUnionApproximation α G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
          H = hLimits.commonEnergy) ∧
        Tendsto
          (fun n : ℕ => Real.log
            ((iidSequenceLaw ν {increment : ℕ → ℝ |
              RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
              stableRateNormalization α ν scale n)
          atTop (𝓝 (C * 2 ^ α * H)) := by
  have hP := hX.isStableClockProcessLaw_unitIntervalPathLaw
  have hlimit : IsAlphaStable α μ := hP.strictlyStable.isAlphaStable
  have hα₂ : α < 2 := by linarith
  have hslow := hDOA.isSlowlyVarying_stableSlowVariation hlimit hα₀ hα₂
  have htail := hDOA.isRegularlyVarying_twoSidedTail hlimit hα₀ hα₂
  have htightBase :=
    FunctionalLimit.Stable.isTightMeasureSet_range_normalizedStepPathLaw_of_index_lt_one
      hscale.stableNorming hα₀ hα₁ htail
  rcases tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_stableInputs
      hscale hα₀ (by linarith) hslow hX hcdf hDOA htightBase hG hGmeas with
    ⟨C, hEscape, hResult⟩
  exact ⟨C, hEscape, hResult⟩

/-- Stable-domain Mogul'skii theorem at index one under the source's
additional sine-centering condition. -/
theorem tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_index_one
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale 1 ν normalization scale)
    {XΩ : Type*} [MeasurableSpace XΩ]
    {X : ℝ≥0 → XΩ → ℝ} {Q : Measure XΩ} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess 1 μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hcenter : IsMogulskiiIndexOneCentered ν normalization)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation 1 G)
    (hGmeas : MeasurableSet G) :
    ∃ C, HasStableProcessEscapeRate 1 μ
      (hX.unitIntervalPathLaw : Measure (CadlagPath unitInterval ℝ)) C ∧
      (∀ n : ℕ,
        NullMeasurableSet
          {increment : ℕ → ℝ |
            RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}
          (iidSequenceLaw ν)) ∧
      ∃! H : ℝ,
        (∃ A : FiniteCorridorUnionApproximation 1 G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
          H = hLimits.commonEnergy) ∧
        Tendsto
          (fun n : ℕ => Real.log
            ((iidSequenceLaw ν {increment : ℕ → ℝ |
              RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
              stableRateNormalization 1 ν scale n)
          atTop (𝓝 (C * 2 ^ (1 : ℝ) * H)) := by
  have hP := hX.isStableClockProcessLaw_unitIntervalPathLaw
  have hlimit : IsAlphaStable 1 μ := hP.strictlyStable.isAlphaStable
  have hslow := hDOA.isSlowlyVarying_stableSlowVariation hlimit (by norm_num) (by norm_num)
  have htail := hDOA.isRegularlyVarying_twoSidedTail hlimit (by norm_num) (by norm_num)
  have htightBase :=
    FunctionalLimit.Stable.isTightMeasureSet_range_normalizedStepPathLaw_of_index_one
      hscale.stableNorming htail hcenter
  rcases tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_stableInputs
      hscale (by norm_num) (by norm_num) hslow hX hcdf hDOA htightBase hG hGmeas with
    ⟨C, hEscape, hResult⟩
  exact ⟨C, hEscape, hResult⟩

/-- Stable-domain Mogul'skii theorem for indices strictly between one and
two.  The domain-of-attraction hypotheses imply finite first moment and zero
mean, which are exactly the hypotheses used by the J₁ tightness criterion.
-/
theorem tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_index_gt_one
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα₀ : 0 < α) (hα₁ : 1 < α) (hα₂ : α < 2)
    {XΩ : Type*} [MeasurableSpace XΩ]
    {X : ℝ≥0 → XΩ → ℝ} {Q : Measure XΩ} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G)
    (hGmeas : MeasurableSet G) :
    ∃ C, HasStableProcessEscapeRate α μ
      (hX.unitIntervalPathLaw : Measure (CadlagPath unitInterval ℝ)) C ∧
      (∀ n : ℕ,
        NullMeasurableSet
          {increment : ℕ → ℝ |
            RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}
          (iidSequenceLaw ν)) ∧
      ∃! H : ℝ,
        (∃ A : FiniteCorridorUnionApproximation α G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
          H = hLimits.commonEnergy) ∧
        Tendsto
          (fun n : ℕ => Real.log
            ((iidSequenceLaw ν {increment : ℕ → ℝ |
              RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
              stableRateNormalization α ν scale n)
          atTop (𝓝 (C * 2 ^ α * H)) := by
  have hP := hX.isStableClockProcessLaw_unitIntervalPathLaw
  have hlimit : IsAlphaStable α μ := hP.strictlyStable.isAlphaStable
  have hslow := hDOA.isSlowlyVarying_stableSlowVariation hlimit hα₀ hα₂
  have htail := hDOA.isRegularlyVarying_twoSidedTail hlimit hα₀ hα₂
  have hint : Integrable (fun x : ℝ => x) ν :=
    integrable_id_of_twoSidedTail_regularlyVarying hα₁ htail
  have hmean := hDOA.integral_eq_zero_of_index_gt_one
    hlimit hscale.stableNorming hα₁ hα₂
  have htightBase :=
    FunctionalLimit.Stable.isTightMeasureSet_range_normalizedStepPathLaw_of_index_gt_one
      hscale.stableNorming hα₀ hα₁ hα₂ htail hint hmean
  rcases tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_stableInputs
      hscale hα₀ (le_of_lt hα₂) hslow hX hcdf hDOA htightBase hG hGmeas with
    ⟨C, hEscape, hResult⟩
  exact ⟨C, hEscape, hResult⟩

/-- Gaussian-domain Mogul'skii theorem at the normal endpoint `α = 2`.
This includes infinite-variance increment laws: the Gaussian domain of
attraction supplies the slowly varying truncated-moment factor, and the
normal-domain `J₁` criterion supplies tightness. -/
theorem tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_index_two
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale 2 ν normalization scale)
    {XΩ : Type*} [MeasurableSpace XΩ]
    {X : ℝ≥0 → XΩ → ℝ} {Q : Measure XΩ} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess 2 (gaussianReal 0 1) X Q)
    (hDOA : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization (fun _ => 0))
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation 2 G)
    (hGmeas : MeasurableSet G) :
    ∃ C, HasStableProcessEscapeRate 2 (gaussianReal 0 1)
      (hX.unitIntervalPathLaw : Measure (CadlagPath unitInterval ℝ)) C ∧
      (∀ n : ℕ,
        NullMeasurableSet
          {increment : ℕ → ℝ |
            RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}
          (iidSequenceLaw ν)) ∧
      ∃! H : ℝ,
        (∃ A : FiniteCorridorUnionApproximation 2 G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
          H = hLimits.commonEnergy) ∧
        Tendsto
          (fun n : ℕ => Real.log
            ((iidSequenceLaw ν {increment : ℕ → ℝ |
              RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
                stableRateNormalization 2 ν scale n)
          atTop (𝓝 (C * 2 ^ (2 : ℝ) * H)) := by
  have hslow := hDOA.stableSlowVariation_two_isSlowlyVarying_of_gaussian
  have hnormalization : ∀ n, 0 < n → 0 < normalization n :=
    hscale.stableNorming.1
  have htightBase :=
    FunctionalLimit.Normal.isTightMeasureSet_range_normalizedStepPathLaw_of_gaussian
      hDOA hnormalization
  have hcdf : 0 < cdf (gaussianReal 0 1) 0 ∧
      cdf (gaussianReal 0 1) 0 < 1 := by
    exact cdf_gaussianReal_zero_lt_one (v := 1) (by norm_num)
  rcases tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_stableInputs
      hscale (by norm_num) (by norm_num) hslow hX hcdf hDOA
      htightBase hG hGmeas with
    ⟨C, hEscape, hResult⟩
  exact ⟨C, hEscape, hResult⟩

/-- Source-level exponent-two Mogul'skii theorem for a Mathlib Brownian
process. This exposes the full path-class conclusion under the normal-domain
of-attraction hypotheses, including laws with infinite variance. -/
theorem tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_index_two_of_brownian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale 2 ν normalization scale)
    (hDOA : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization (fun _ => 0))
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B Q)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation 2 G)
    (hGmeas : MeasurableSet G) :
    ∃ C, HasStableProcessEscapeRate 2 (gaussianReal 0 1)
        (Process.Path.Cadlag.pathLaw Q
          (fun t ω => B (UnitInterval.toNNReal t) ω)
          (fun t => hB.toIsPreBrownianReal.aemeasurable
            (UnitInterval.toNNReal t))) C ∧
      (∀ n : ℕ,
        NullMeasurableSet
          {increment : ℕ → ℝ |
            RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}
          (iidSequenceLaw ν)) ∧
      ∃! H : ℝ,
        (∃ A : FiniteCorridorUnionApproximation 2 G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
          H = hLimits.commonEnergy) ∧
        Tendsto
          (fun n : ℕ => Real.log
            ((iidSequenceLaw ν {increment : ℕ → ℝ |
              RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
                stableRateNormalization 2 ν scale n)
          atTop (𝓝 (C * 2 ^ (2 : ℝ) * H)) := by
  exact tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_index_two
    hscale hB.isStableLevyProcess hDOA hG hGmeas

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

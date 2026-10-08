/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PathClassRate
import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLimit.Source
import Probability.Process.RandomWalk.FunctionalLimit.Stable.Centering
import Probability.Distributions.Stable.Attraction.NormingRatios.Tauberian

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

open ProbabilityTheory.Process.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

/-- Main stable-domain path-class theorem, with tightness and the slowly
varying factor supplied as explicit inputs.  The exact target-set event is
measurable because `G` is Borel and every finite-step path map is measurable.
-/
theorem tendsto_log_probability_ratio_of_IsM_of_stableInputs
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    {XΩ : Type*} [MeasurableSpace XΩ]
    {X : ℝ≥0 → XΩ → ℝ} {Q : Measure XΩ} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    {G : Set (CadlagPath unitInterval ℝ)} (hG : IsM α G)
    (hGmeas : MeasurableSet G) :
    ∃ C, HasStableProcessEscapeRate α μ P C ∧
      (∀ n : ℕ,
        NullMeasurableSet
          {increment : ℕ → ℝ |
            RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}
          (iidSequenceLaw ν)) ∧
      ∃! H : ℝ,
        (∃ A : M3Approximation α G, ∃ hLimits : M3EnergyLimits A,
          H = hLimits.hAlpha) ∧
        Tendsto
          (fun n : ℕ => Real.log
            ((iidSequenceLaw ν {increment : ℕ → ℝ |
              RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
              stableRateNormalization α ν scale n)
          atTop (𝓝 (C * 2 ^ α * H)) := by
  obtain ⟨C, hEscape⟩ :=
    hP.hasStableProcessEscapeRate_of_isStableLevyProcess hX hcdf
  have hGnull : ∀ n : ℕ,
      NullMeasurableSet
        {increment : ℕ → ℝ |
          RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}
        (iidSequenceLaw ν) := by
    intro n
    have hpath : Measurable (RandomWalk.normalizedStepCadlagPathIcc scale n) :=
      RandomWalk.measurable_normalizedStepCadlagPathIcc scale n
    exact (hGmeas.preimage hpath).nullMeasurableSet
  have hresult := tendsto_log_probability_ratio_of_IsM_of_discreteM2Rates
    hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase hG hGnull
  rcases hresult.2 with ⟨H, hH, hUnique⟩
  have hratePos := stableSmallDeviationRate_pos_eventually hscale hslow
  have hsource := tendsto_log_div_stableRateNormalization_of_neg hratePos hH.2
  have hcoef : -(stableProcessMogulskiiCoefficient α C * H) =
      C * 2 ^ α * H := by
    simp [stableProcessMogulskiiCoefficient]
  refine ⟨C, hEscape, hresult.1, H, ⟨hH.1, ?_⟩, ?_⟩
  · simpa [hcoef] using hsource
  · intro H' hH'
    apply hUnique H'
    refine ⟨hH'.1, ?_⟩
    have hnegative :=
      tendsto_log_div_probabilityRateDenominator_of_stableRateNormalization
        hratePos hH'.2
    have hcoef' : -(C * 2 ^ α * H') =
        stableProcessMogulskiiCoefficient α C * H' := by
      simp [stableProcessMogulskiiCoefficient]
    simpa [hcoef'] using hnegative

/-- Stable-domain Mogul'skii theorem below index one.  Regular variation of
the tails gives the J₁ tightness criterion; the stable-domain Tauberian result
gives the slowly varying factor used in the small-deviation normalization.
-/
theorem tendsto_log_probability_ratio_of_IsM_of_index_lt_one
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    {XΩ : Type*} [MeasurableSpace XΩ]
    {X : ℝ≥0 → XΩ → ℝ} {Q : Measure XΩ} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    {G : Set (CadlagPath unitInterval ℝ)} (hG : IsM α G)
    (hGmeas : MeasurableSet G) :
    ∃ C, HasStableProcessEscapeRate α μ P C ∧
      (∀ n : ℕ,
        NullMeasurableSet
          {increment : ℕ → ℝ |
            RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}
          (iidSequenceLaw ν)) ∧
      ∃! H : ℝ,
        (∃ A : M3Approximation α G, ∃ hLimits : M3EnergyLimits A,
          H = hLimits.hAlpha) ∧
        Tendsto
          (fun n : ℕ => Real.log
            ((iidSequenceLaw ν {increment : ℕ → ℝ |
              RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
              stableRateNormalization α ν scale n)
          atTop (𝓝 (C * 2 ^ α * H)) := by
  have hlimit : IsAlphaStable α μ := hP.strictlyStable.isAlphaStable
  have hα₂ : α < 2 := by linarith
  have hslow := hDOA.isSlowlyVarying_stableSlowVariation hlimit hα₀ hα₂
  have htail := hDOA.isRegularlyVarying_twoSidedTail hlimit hα₀ hα₂
  have htightBase :=
    FunctionalLimit.Stable.isTightMeasureSet_range_normalizedStepPathLaw_of_index_lt_one
      hscale.stableNorming hα₀ hα₁ htail
  rcases tendsto_log_probability_ratio_of_IsM_of_stableInputs
      hscale hα₀ (by linarith) hslow hP hX hcdf hDOA htightBase hG hGmeas with
    ⟨C, hEscape, hResult⟩
  exact ⟨C, hEscape, hResult⟩

/-- Stable-domain Mogul'skii theorem at index one under the source's
additional sine-centering condition. -/
theorem tendsto_log_probability_ratio_of_IsM_of_index_one
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale 1 ν normalization scale)
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw 1 μ unitIntervalClock P)
    {XΩ : Type*} [MeasurableSpace XΩ]
    {X : ℝ≥0 → XΩ → ℝ} {Q : Measure XΩ} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess 1 μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hcenter : IsMogulskiiIndexOneCentered ν normalization)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : IsM 1 G)
    (hGmeas : MeasurableSet G) :
    ∃ C, HasStableProcessEscapeRate 1 μ P C ∧
      (∀ n : ℕ,
        NullMeasurableSet
          {increment : ℕ → ℝ |
            RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}
          (iidSequenceLaw ν)) ∧
      ∃! H : ℝ,
        (∃ A : M3Approximation 1 G, ∃ hLimits : M3EnergyLimits A,
          H = hLimits.hAlpha) ∧
        Tendsto
          (fun n : ℕ => Real.log
            ((iidSequenceLaw ν {increment : ℕ → ℝ |
              RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
              stableRateNormalization 1 ν scale n)
          atTop (𝓝 (C * 2 ^ (1 : ℝ) * H)) := by
  have hlimit : IsAlphaStable 1 μ := hP.strictlyStable.isAlphaStable
  have hslow := hDOA.isSlowlyVarying_stableSlowVariation hlimit (by norm_num) (by norm_num)
  have htail := hDOA.isRegularlyVarying_twoSidedTail hlimit (by norm_num) (by norm_num)
  have htightBase :=
    FunctionalLimit.Stable.isTightMeasureSet_range_normalizedStepPathLaw_of_index_one
      hscale.stableNorming htail hcenter
  rcases tendsto_log_probability_ratio_of_IsM_of_stableInputs
      hscale (by norm_num) (by norm_num) hslow hP hX hcdf hDOA htightBase hG hGmeas with
    ⟨C, hEscape, hResult⟩
  exact ⟨C, hEscape, hResult⟩

/-- Stable-domain Mogul'skii theorem for indices strictly between one and
two.  The domain-of-attraction hypotheses imply finite first moment and zero
mean, which are exactly the hypotheses used by the J₁ tightness criterion.
-/
theorem tendsto_log_probability_ratio_of_IsM_of_index_gt_one
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα₀ : 0 < α) (hα₁ : 1 < α) (hα₂ : α < 2)
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    {XΩ : Type*} [MeasurableSpace XΩ]
    {X : ℝ≥0 → XΩ → ℝ} {Q : Measure XΩ} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    {G : Set (CadlagPath unitInterval ℝ)} (hG : IsM α G)
    (hGmeas : MeasurableSet G) :
    ∃ C, HasStableProcessEscapeRate α μ P C ∧
      (∀ n : ℕ,
        NullMeasurableSet
          {increment : ℕ → ℝ |
            RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}
          (iidSequenceLaw ν)) ∧
      ∃! H : ℝ,
        (∃ A : M3Approximation α G, ∃ hLimits : M3EnergyLimits A,
          H = hLimits.hAlpha) ∧
        Tendsto
          (fun n : ℕ => Real.log
            ((iidSequenceLaw ν {increment : ℕ → ℝ |
              RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
              stableRateNormalization α ν scale n)
          atTop (𝓝 (C * 2 ^ α * H)) := by
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
  rcases tendsto_log_probability_ratio_of_IsM_of_stableInputs
      hscale hα₀ (le_of_lt hα₂) hslow hP hX hcdf hDOA htightBase hG hGmeas with
    ⟨C, hEscape, hResult⟩
  exact ⟨C, hEscape, hResult⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

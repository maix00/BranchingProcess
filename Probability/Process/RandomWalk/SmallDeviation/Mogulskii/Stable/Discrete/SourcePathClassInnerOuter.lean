/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourcePathClassRate
import Probability.Distributions.Gaussian.Interval
import Probability.Distributions.Stable.Attraction.NormingRatios.Tauberian
import Probability.Process.RandomWalk.FunctionalLimit.Normal.Tightness
import Probability.Process.RandomWalk.FunctionalLimit.Stable.Centering
import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLimit.Source
import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.InnerOuter
import Probability.Process.Stable.PathLaw.UnitInterval

/-!
# Source-convention inner and outer probability rates

The source endpoint version of the exact M₂ estimate feeds the same M₃
approximation squeeze. This gives a rate for both inner and outer probabilities
without assuming the target set is measurable.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

/-- The common source-convention inner/outer rate conclusion. Keeping this
package named lets the stable-input theorem and its index-regime specializations
share one public result type. -/
abbrev SourceInnerOuterRateConclusion
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (α : ℝ) (scale : ℕ → ℝ)
    (P : Measure (CadlagPath unitInterval ℝ)) (hP : IsProbabilityMeasure P)
    (G : Set (CadlagPath unitInterval ℝ)) : Prop :=
  letI : IsProbabilityMeasure P := hP
  ∃ C, HasStableProcessEscapeRate α μ P C ∧
    ∃! H : ℝ,
      ∃ A : FiniteCorridorUnionApproximation α G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
        H = hLimits.commonEnergy ∧
        (∀ᶠ n : ℕ in atTop,
          0 < ((iidSequenceLaw ν).innerMeasure
            {increment : ℕ → ℝ |
              RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
        (∀ᶠ n : ℕ in atTop,
          0 < (iidSequenceLaw ν
            {increment : ℕ → ℝ |
              RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
        0 < H ∧ H ≤ FiniteCorridorUnion.realEnergy (A.inner 0) ∧
        Tendsto
          (fun n : ℕ => Real.log
            (((iidSequenceLaw ν).innerMeasure
              {increment : ℕ → ℝ |
                RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
                probabilityRateDenominator α ν scale n)
          atTop (𝓝 (rateCoefficient α C * H)) ∧
        Tendsto
          (fun n : ℕ => Real.log
            ((iidSequenceLaw ν
              {increment : ℕ → ℝ |
                RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
                probabilityRateDenominator α ν scale n)
          atTop (𝓝 (rateCoefficient α C * H))

/-- For every path set in the source class `M`, its inner and outer
probabilities along the source terminal-left random-walk paths have the same
unique logarithmic rate. No measurability assumption on the target is made. -/
theorem existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_sourceDiscretestepCorridorRates
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {XΩ : Type*} [MeasurableSpace XΩ]
    {X : ℝ≥0 → XΩ → ℝ} {Q : Measure XΩ} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G) :
    ∃! H : ℝ,
      ∃ A : FiniteCorridorUnionApproximation α G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
        H = hLimits.commonEnergy ∧
        (∀ᶠ n : ℕ in atTop,
          0 < ((iidSequenceLaw ν).innerMeasure
            {increment : ℕ → ℝ |
              RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
        (∀ᶠ n : ℕ in atTop,
          0 < (iidSequenceLaw ν
            {increment : ℕ → ℝ |
              RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
        0 < H ∧ H ≤ FiniteCorridorUnion.realEnergy (A.inner 0) ∧
        Tendsto
          (fun n : ℕ => Real.log
            (((iidSequenceLaw ν).innerMeasure
              {increment : ℕ → ℝ |
                RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
                probabilityRateDenominator α ν scale n)
          atTop (𝓝 (rateCoefficient α C * H)) ∧
        Tendsto
          (fun n : ℕ => Real.log
            ((iidSequenceLaw ν
              {increment : ℕ → ℝ |
                RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
                probabilityRateDenominator α ν scale n)
          atTop (𝓝 (rateCoefficient α C * H)) := by
  let paths : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ := fun n increment =>
    RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment
  let denominator : ℕ → ℝ := probabilityRateDenominator α ν scale
  let κ : ℝ := rateCoefficient α C
  have hκ : 0 < κ := rateCoefficient_pos hEscape.negative
  have hdenom : Tendsto denominator atTop atBot := by
    simpa [denominator] using sourceProbabilityRateDenominator_tendsto_atBot
      hscale hα hα₂ hslow
  have hStepCorridorRate : ∀ c : ContinuousAdmissibleStepCorridor,
      (∀ n : ℕ, NullMeasurableSet
        {increment : ℕ → ℝ | paths n increment ∈ c.toSet}
        (iidSequenceLaw ν)) ∧
      (∀ᶠ n : ℕ in atTop,
        0 < (iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) ∧
      Tendsto (fun n : ℕ => Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) /
            denominator n)
        atTop (𝓝 (κ * (ContinuousAdmissibleStepCorridor.energy α c).toReal)) := by
    intro c
    simpa [paths, denominator, κ] using
      sourceNormalizedStepCorridor_admissibleStepCorridor_rate hscale hα hα₂ hslow hEscape hX hcdf
        hDOA htightBase c
  have hFiniteUnionRate : ∀ C₃ : FiniteCorridorUnion α,
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
    let hpieces := fun i : Fin C₃.count => hStepCorridorRate (C₃.pieces i)
    have h := tendsto_log_finiteCorridorUnion_preimage_probability_ratio_of_nullMeasurable
      (iidSequenceLaw ν) C₃ paths denominator hdenom hκ
      (fun n i => (hpieces i).1 n)
      (fun i => (hpieces i).2.1)
      (fun i => by simpa [FiniteCorridorUnion.realEnergy] using (hpieces i).2.2)
    exact ⟨h.1, h.2.1, h.2.2⟩
  have hUnique := existsUnique_commonEnergy_of_hasVanishingEnergyGapApproximation
    (iidSequenceLaw ν) paths denominator hdenom hκ hG hFiniteUnionRate
  obtain ⟨A, hLimits, hInnerPos, hOuterPos, hInnerRate, hOuterRate,
      hEnergyBounds⟩ :=
    exists_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation
      (iidSequenceLaw ν) paths denominator hdenom hκ hG hFiniteUnionRate
  let H : ℝ := hLimits.commonEnergy
  refine ⟨H, ?_, ?_⟩
  · refine ⟨A, hLimits, rfl, hInnerPos, hOuterPos, hEnergyBounds.1,
      hEnergyBounds.2, ?_, ?_⟩
    · simpa [paths, denominator, κ, H] using hInnerRate
    · simpa [paths, denominator, κ, H] using hOuterRate
  · intro H' hH'
    obtain ⟨A', hLimits', hEq', _hInnerPos', _hOuterPos', _hPosRate',
      _hEnergyUpper', _hInnerRate', _hOuterRate'⟩ := hH'
    have hEq := hUnique.unique ⟨A', hLimits', hEq'⟩ ⟨A, hLimits, rfl⟩
    exact hEq

/-- Source-aligned inner/outer probability theorem from an actual stable
Lévy-process realization. The unit-interval path law and the stable escape
rate are derived internally; the caller does not provide a separate path-law
witness. -/
theorem existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_sourceStableInputs
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
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G) :
    SourceInnerOuterRateConclusion (ν := ν) (μ := μ) α scale
      (hX.unitIntervalPathLaw : Measure (CadlagPath unitInterval ℝ))
      hX.unitIntervalPathLaw.property G := by
  obtain ⟨C, hEscape⟩ :=
    hX.isStableClockProcessLaw_unitIntervalPathLaw
      |>.hasStableProcessEscapeRate_of_isStableLevyProcess hX hcdf
  exact ⟨C, hEscape,
    existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_sourceDiscretestepCorridorRates
      hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase hG⟩

/-- Source-convention inner/outer theorem below index one. Slow variation and
tightness are derived from the attraction assumptions. -/
theorem existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_source_index_lt_one
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    {XΩ : Type*} [MeasurableSpace XΩ]
    {X : ℝ≥0 → XΩ → ℝ} {Q : Measure XΩ} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G) :
    SourceInnerOuterRateConclusion (ν := ν) (μ := μ) α scale
      (hX.unitIntervalPathLaw : Measure (CadlagPath unitInterval ℝ))
      hX.unitIntervalPathLaw.property G := by
  have hP := hX.isStableClockProcessLaw_unitIntervalPathLaw
  have hlimit : IsAlphaStable α μ := hP.strictlyStable.isAlphaStable
  have hα₂ : α < 2 := by linarith
  have hslow := hDOA.isSlowlyVarying_stableSlowVariation hlimit hα₀ hα₂
  have htail := hDOA.isRegularlyVarying_twoSidedTail hlimit hα₀ hα₂
  have htightBase :=
    FunctionalLimit.Stable.isTightMeasureSet_range_normalizedStepPathLaw_of_index_lt_one
      hscale.stableNorming hα₀ hα₁ htail
  exact existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_sourceStableInputs
    hscale hα₀ (by linarith) hslow hX hcdf hDOA htightBase hG

/-- Source-convention inner/outer theorem at index one, under the source's
additional sine-centering condition. -/
theorem existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_source_index_one
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale 1 ν normalization scale)
    {XΩ : Type*} [MeasurableSpace XΩ]
    {X : ℝ≥0 → XΩ → ℝ} {Q : Measure XΩ} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess 1 μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hcenter : IsMogulskiiIndexOneCentered ν normalization)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation 1 G) :
    SourceInnerOuterRateConclusion (ν := ν) (μ := μ) 1 scale
      (hX.unitIntervalPathLaw : Measure (CadlagPath unitInterval ℝ))
      hX.unitIntervalPathLaw.property G := by
  have hP := hX.isStableClockProcessLaw_unitIntervalPathLaw
  have hlimit : IsAlphaStable 1 μ := hP.strictlyStable.isAlphaStable
  have hslow := hDOA.isSlowlyVarying_stableSlowVariation hlimit (by norm_num) (by norm_num)
  have htail := hDOA.isRegularlyVarying_twoSidedTail hlimit (by norm_num) (by norm_num)
  have htightBase :=
    FunctionalLimit.Stable.isTightMeasureSet_range_normalizedStepPathLaw_of_index_one
      hscale.stableNorming htail hcenter
  exact existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_sourceStableInputs
    hscale (by norm_num) (by norm_num) hslow hX hcdf hDOA htightBase hG

/-- Source-convention inner/outer theorem for indices strictly between one
and two. -/
theorem existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_source_index_gt_one
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα₀ : 0 < α) (hα₁ : 1 < α) (hα₂ : α < 2)
    {XΩ : Type*} [MeasurableSpace XΩ]
    {X : ℝ≥0 → XΩ → ℝ} {Q : Measure XΩ} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G) :
    SourceInnerOuterRateConclusion (ν := ν) (μ := μ) α scale
      (hX.unitIntervalPathLaw : Measure (CadlagPath unitInterval ℝ))
      hX.unitIntervalPathLaw.property G := by
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
  exact existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_sourceStableInputs
    hscale hα₀ (le_of_lt hα₂) hslow hX hcdf hDOA htightBase hG

/-- Source-convention inner/outer theorem at index two. The attraction input
may come from a normal domain of attraction with infinite variance. -/
theorem existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_source_index_two
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale 2 ν normalization scale)
    {XΩ : Type*} [MeasurableSpace XΩ]
    {X : ℝ≥0 → XΩ → ℝ}
    {Q : Measure XΩ} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess 2 (gaussianReal 0 1) X Q)
    (hDOA : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization (fun _ => 0))
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation 2 G) :
    SourceInnerOuterRateConclusion (ν := ν) (μ := gaussianReal 0 1) 2 scale
      (hX.unitIntervalPathLaw : Measure (CadlagPath unitInterval ℝ))
      hX.unitIntervalPathLaw.property G := by
  have hslow := hDOA.stableSlowVariation_two_isSlowlyVarying_of_gaussian
  have hnormalization : ∀ n, 0 < n → 0 < normalization n :=
    hscale.stableNorming.1
  have htightBase :=
    FunctionalLimit.Normal.isTightMeasureSet_range_normalizedStepPathLaw_of_gaussian
      hDOA hnormalization
  have hcdf : 0 < cdf (gaussianReal 0 1) 0 ∧
      cdf (gaussianReal 0 1) 0 < 1 :=
    cdf_gaussianReal_zero_lt_one (v := 1) (by norm_num)
  exact existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_sourceStableInputs
    hscale (by norm_num) (by norm_num) hslow hX hcdf hDOA htightBase hG

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

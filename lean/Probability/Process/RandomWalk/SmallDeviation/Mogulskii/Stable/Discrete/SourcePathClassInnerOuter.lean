/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourcePathClassRate
import Probability.Process.SmallDeviation.Mogulskii.PathClass.Rate.InnerOuter
import Probability.Process.Stable.PathLaw.UnitInterval

/-!
# Source-convention inner and outer probability rates

The source endpoint version of the exact M₂ estimate feeds the same M₃
approximation squeeze. This gives a rate for both inner and outer probabilities
without assuming the target set is measurable.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.Process.SmallDeviation.Mogulskii

/-- For every path set in the source class `M`, its inner and outer
probabilities along the source terminal-left random-walk paths have the same
unique logarithmic rate. No measurability assumption on the target is made. -/
theorem existsUnique_inner_outer_log_probability_ratio_of_IsM_of_sourceDiscreteM2Rates
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
    {G : Set (CadlagPath unitInterval ℝ)} (hG : IsM α G) :
    ∃! H : ℝ,
      ∃ A : M3Approximation α G, ∃ hLimits : M3EnergyLimits A,
        H = hLimits.hAlpha ∧
        (∀ᶠ n : ℕ in atTop,
          0 < ((iidSequenceLaw ν).innerMeasure
            {increment : ℕ → ℝ |
              RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
        (∀ᶠ n : ℕ in atTop,
          0 < (iidSequenceLaw ν
            {increment : ℕ → ℝ |
              RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
        0 < H ∧ H ≤ M3.hAlpha (A.inner 0) ∧
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
  have hM2rate : ∀ c : M2Corridor,
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
        atTop (𝓝 (κ * (M2Corridor.energy α c).toReal)) := by
    intro c
    simpa [paths, denominator, κ] using
      sourceNormalizedStepCorridor_m2_rate hscale hα hα₂ hslow hEscape hX hcdf
        hDOA htightBase c
  have hM3rate : ∀ C₃ : M3 α,
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
        atTop (𝓝 (κ * C₃.hAlpha)) := by
    intro C₃
    let hpieces := fun i : Fin C₃.count => hM2rate (C₃.pieces i)
    have h := tendsto_log_m3_preimage_probability_ratio_of_nullMeasurable
      (iidSequenceLaw ν) C₃ paths denominator hdenom hκ
      (fun n i => (hpieces i).1 n)
      (fun i => (hpieces i).2.1)
      (fun i => by simpa [M3.hAlpha] using (hpieces i).2.2)
    exact ⟨h.1, h.2.1, h.2.2⟩
  have hUnique := existsUnique_hAlpha_of_IsM
    (iidSequenceLaw ν) paths denominator hdenom hκ hG hM3rate
  obtain ⟨A, hLimits, hInnerPos, hOuterPos, hInnerRate, hOuterRate,
      hEnergyBounds⟩ :=
    exists_inner_outer_log_probability_ratio_of_IsM
      (iidSequenceLaw ν) paths denominator hdenom hκ hG hM3rate
  let H : ℝ := hLimits.hAlpha
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
theorem existsUnique_inner_outer_log_probability_ratio_of_IsM_of_sourceStableInputs
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
    {G : Set (CadlagPath unitInterval ℝ)} (hG : IsM α G) :
    ∃ C, HasStableProcessEscapeRate α μ
      (hX.unitIntervalPathLaw : Measure (CadlagPath unitInterval ℝ)) C ∧
      ∃! H : ℝ,
        ∃ A : M3Approximation α G, ∃ hLimits : M3EnergyLimits A,
          H = hLimits.hAlpha ∧
          (∀ᶠ n : ℕ in atTop,
            0 < ((iidSequenceLaw ν).innerMeasure
              {increment : ℕ → ℝ |
                RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
          (∀ᶠ n : ℕ in atTop,
            0 < (iidSequenceLaw ν
              {increment : ℕ → ℝ |
                RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
          0 < H ∧ H ≤ M3.hAlpha (A.inner 0) ∧
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
  obtain ⟨C, hEscape⟩ :=
    hX.isStableClockProcessLaw_unitIntervalPathLaw
      |>.hasStableProcessEscapeRate_of_isStableLevyProcess hX hcdf
  exact ⟨C, hEscape,
    existsUnique_inner_outer_log_probability_ratio_of_IsM_of_sourceDiscreteM2Rates
      hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase hG⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

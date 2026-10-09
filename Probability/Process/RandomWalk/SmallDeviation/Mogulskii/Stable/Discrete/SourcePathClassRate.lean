/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PathClassRate
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourcePartitionLimit
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.Approximation

/-!
# Path-class rates for the source endpoint convention

The source path records the partial sums through `n - 1`. This file transfers
the exact source-normalized `M₂` corridor rates to the general `M` class using
the shared finite-union and approximation theorems.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Skorokhod.PathClass.StepCorridor

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

theorem sourceProbabilityRateDenominator_tendsto_atBot
    {α : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν)) :
    Tendsto (probabilityRateDenominator α ν scale) atTop atBot := by
  let rate : ℕ → ℝ := stableSmallDeviationRate α ν scale
  have hrateZero : Tendsto rate atTop (𝓝 0) :=
    tendsto_stableSmallDeviationRate_zero_of_slowVariation
      hscale.stableNorming hscale.scale_tendsto_atTop
      hscale.scale_div_normalization_tendsto_zero hα hα₂ hslow
  have hratePos : ∀ᶠ n : ℕ in atTop, 0 < rate n :=
    stableSmallDeviationRate_pos_eventually hscale hslow
  have hrateRight : Tendsto rate atTop (𝓝[>] (0 : ℝ)) := by
    rw [nhdsWithin, tendsto_inf]
    exact ⟨hrateZero, tendsto_principal.2 hratePos⟩
  have hinv : Tendsto (fun n => (rate n)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp hrateRight
  exact tendsto_neg_atTop_atBot.comp hinv

/-- Under the source endpoint convention, every finite-partition `M₂`
corridor has the exact logarithmic rate. The event is null-measurable by the
measurable source path map and the general path-space corridor result. -/
theorem sourceNormalizedStepCorridor_admissibleStepCorridor_rate
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (c : ContinuousAdmissibleStepCorridor) :
    (∀ n : ℕ, NullMeasurableSet
      {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ c.toSet}
      (iidSequenceLaw ν)) ∧
    (∀ᶠ n : ℕ in atTop, 0 < (iidSequenceLaw ν
      {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ c.toSet}).toReal) ∧
    Tendsto (fun n : ℕ => Real.log ((iidSequenceLaw ν
      {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ c.toSet}).toReal) /
        probabilityRateDenominator α ν scale n)
      atTop (𝓝 (rateCoefficient α C * (c.energy α).toReal)) := by
  let paths : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ := fun n increment =>
    RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment
  have hdiscrete := tendsto_scaledLog_sourceNormalizedStepCorridor_eq_energyRate
    hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase c
  have hEvent (n : ℕ) :
      {increment : ℕ → ℝ | paths n increment ∈ c.toSet} =
        {increment : ℕ → ℝ |
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
            corridorSet c.upper c.lower} := by
    ext increment
    simp [paths, ContinuousAdmissibleStepCorridor.toSet, FiniteStepCorridor.toSet]
  have hnull : ∀ n : ℕ,
      NullMeasurableSet {increment : ℕ → ℝ | paths n increment ∈ c.toSet}
        (iidSequenceLaw ν) := by
    intro n
    exact ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability.ContinuousAdmissibleStepCorridor.nullMeasurableSet_preimage_toSet_of_aemeasurable
      c (iidSequenceLaw ν) (paths n) (by
        dsimp [paths]
        exact RandomWalk.measurable_sourceNormalizedStepCadlagPathIcc scale n
          |>.aemeasurable)
  have hpositive : ∀ᶠ n : ℕ in atTop,
      0 < (iidSequenceLaw ν
        {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal := by
    filter_upwards [hdiscrete.1] with n hn
    rw [hEvent n]
    exact ENNReal.toReal_pos (ne_of_gt hn) (measure_ne_top _ _)
  have hratePos : ∀ᶠ n : ℕ in atTop,
      0 < stableSmallDeviationRate α ν scale n :=
    stableSmallDeviationRate_pos_eventually hscale hslow
  have hlograte : Tendsto (fun n : ℕ => stableSmallDeviationRate α ν scale n *
      Real.log ((iidSequenceLaw ν
        {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal))
      atTop (𝓝 (C * 2 ^ α * (c.energy α).toReal)) := by
    have heq : (fun n : ℕ => stableSmallDeviationRate α ν scale n *
        Real.log ((iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal)) =ᶠ[atTop]
        (fun n : ℕ => stableSmallDeviationRate α ν scale n *
          Real.log (iidSequenceLaw ν
            {increment : ℕ → ℝ |
              RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
                corridorSet c.upper c.lower}).toReal) := by
      filter_upwards [] with n
      simp [hEvent n]
    exact hdiscrete.2.congr' heq
  have hratio : Tendsto (fun n : ℕ => Real.log ((iidSequenceLaw ν
      {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) /
        probabilityRateDenominator α ν scale n)
      atTop (𝓝 (rateCoefficient α C * (c.energy α).toReal)) := by
    have heq : (fun n : ℕ => Real.log ((iidSequenceLaw ν
        {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) /
          probabilityRateDenominator α ν scale n) =ᶠ[atTop]
        fun n => -(stableSmallDeviationRate α ν scale n *
          Real.log ((iidSequenceLaw ν
            {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal)) := by
      filter_upwards [hratePos] with n hrate
      have hrateNe : stableSmallDeviationRate α ν scale n ≠ 0 := hrate.ne'
      dsimp [probabilityRateDenominator]
      field_simp [hrateNe]
    have htarget : -(C * 2 ^ α * (c.energy α).toReal) =
        rateCoefficient α C * (c.energy α).toReal := by
      dsimp [rateCoefficient]
      ring
    exact by simpa [htarget] using hlograte.neg.congr' heq.symm
  exact ⟨hnull, ⟨hpositive, hratio⟩⟩

/-- The source endpoint convention has the random-walk Mogul'skii rate for
every null-measurable target in class `M`. The `M₃` and approximation
arguments are shared with the càdlàg path convention. -/
theorem tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_sourceDiscretestepCorridorRates
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
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G)
    (hGnull : ∀ n : ℕ, NullMeasurableSet
      {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}
      (iidSequenceLaw ν)) :
    (∀ n : ℕ, NullMeasurableSet
      {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}
      (iidSequenceLaw ν)) ∧
    ∃! H : ℝ,
      (∃ A : FiniteCorridorUnionApproximation α G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
        H = hLimits.commonEnergy) ∧
      Tendsto (fun n : ℕ => Real.log ((iidSequenceLaw ν
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
  refine ⟨?_, ?_⟩
  · intro n
    simpa [paths] using hGnull n
  · have hresult := tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_stepCorridorRates
      (iidSequenceLaw ν) paths denominator hdenom hκ hG hGnull hStepCorridorRate
    simpa [paths, denominator, κ] using hresult.2

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

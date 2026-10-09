/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PathClassRate
import Probability.Process.SmallDeviation.Mogulskii.PathClass.Rate.FiniteUnionNullMeasurable
import Probability.Process.SmallDeviation.Mogulskii.PathClass.Rate.InnerOuter

/-!
# Discrete path-class rates for inner and outer probabilities

The exact target event of an arbitrary source-class `M` path set need not be
measurable.  The discrete `M₂` estimates give rates for the measurable-up-to-null
`M₃` approximants, which squeeze the inner and outer probabilities to the same
unique logarithmic rate.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.Process.SmallDeviation.Mogulskii

private theorem probabilityRateDenominator_tendsto_atBot_local
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
  have hneg := tendsto_neg_atTop_atBot.comp hinv
  change Tendsto
    (fun n : ℕ => -((stableSmallDeviationRate α ν scale n)⁻¹)) atTop atBot
  exact hneg

/-- The discrete `M₂` rates imply the common logarithmic rate for the inner and
outer probabilities of every source-class `M` path set.  The target event is
not assumed measurable.  The shared energy limit is unique independently of
the chosen `M₃` approximation witness. -/
theorem existsUnique_inner_outer_log_probability_ratio_of_IsM_of_discreteM2Rates
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
              RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
        (∀ᶠ n : ℕ in atTop,
          0 < (iidSequenceLaw ν
            {increment : ℕ → ℝ |
              RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
        0 < H ∧ H ≤ M3.hAlpha (A.inner 0) ∧
        Tendsto
          (fun n : ℕ => Real.log
            (((iidSequenceLaw ν).innerMeasure
              {increment : ℕ → ℝ |
                RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
                probabilityRateDenominator α ν scale n)
          atTop (𝓝 (rateCoefficient α C * H)) ∧
        Tendsto
          (fun n : ℕ => Real.log
            ((iidSequenceLaw ν
              {increment : ℕ → ℝ |
                RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
                probabilityRateDenominator α ν scale n)
          atTop (𝓝 (rateCoefficient α C * H)) := by
  let paths : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ := fun n increment =>
    RandomWalk.normalizedStepCadlagPathIcc scale n increment
  let denominator : ℕ → ℝ := probabilityRateDenominator α ν scale
  let κ : ℝ := rateCoefficient α C

  have hκ : 0 < κ := rateCoefficient_pos hEscape.negative
  have hdenom : Tendsto denominator atTop atBot := by
    simpa [denominator] using probabilityRateDenominator_tendsto_atBot_local
      hscale hα hα₂ hslow
  have hratePos : ∀ᶠ n : ℕ in atTop,
      0 < stableSmallDeviationRate α ν scale n :=
    stableSmallDeviationRate_pos_eventually hscale hslow

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
    have hdiscrete := tendsto_scaledLog_normalizedStepCorridor_eq_energyRate
      hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase c
    have hEvent (n : ℕ) :
        {increment : ℕ → ℝ | paths n increment ∈ c.toSet} =
          {increment : ℕ → ℝ |
            RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
              corridorSet c.upper c.lower} := by
      ext increment
      simp [paths, M2Corridor.toSet, M1Corridor.toSet]
    have hnull : ∀ n : ℕ, NullMeasurableSet
        {increment : ℕ → ℝ | paths n increment ∈ c.toSet}
        (iidSequenceLaw ν) := by
      intro n
      exact c.nullMeasurableSet_preimage_toSet_of_aemeasurable
        (iidSequenceLaw ν) (paths n) (by
          dsimp [paths]
          exact RandomWalk.measurable_normalizedStepCadlagPathIcc scale n
            |>.aemeasurable)
    have hpositive : ∀ᶠ n : ℕ in atTop,
        0 < (iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal := by
      filter_upwards [hdiscrete.1] with n hn
      rw [hEvent n]
      exact ENNReal.toReal_pos (ne_of_gt hn) (measure_ne_top _ _)
    have hlograte : Tendsto (fun n : ℕ =>
        stableSmallDeviationRate α ν scale n * Real.log
          (iidSequenceLaw ν
            {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal)
        atTop (𝓝 (C * 2 ^ α * (M2Corridor.energy α c).toReal)) := by
      have h := hdiscrete.2
      have heq : (fun n : ℕ => stableSmallDeviationRate α ν scale n * Real.log
          (iidSequenceLaw ν
            {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) =ᶠ[atTop]
          (fun n : ℕ => stableSmallDeviationRate α ν scale n * Real.log
            (iidSequenceLaw ν
              {increment : ℕ → ℝ |
                RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
                  corridorSet c.upper c.lower}).toReal) := by
        filter_upwards [] with n
        simp [hEvent n]
      exact h.congr' heq
    have hratio : Tendsto (fun n : ℕ => Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) /
            denominator n)
        atTop (𝓝 (κ * (M2Corridor.energy α c).toReal)) := by
      have heq : (fun n : ℕ => Real.log
          ((iidSequenceLaw ν
            {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) /
              denominator n) =ᶠ[atTop]
          (fun n : ℕ => -(stableSmallDeviationRate α ν scale n * Real.log
            (iidSequenceLaw ν
              {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal)) := by
        filter_upwards [hratePos] with n hrate
        have hrateNe : stableSmallDeviationRate α ν scale n ≠ 0 := hrate.ne'
        dsimp [denominator, probabilityRateDenominator]
        field_simp [hrateNe]
      have hneg := hlograte.neg
      have htarget : -(C * 2 ^ α * (M2Corridor.energy α c).toReal) =
          κ * (M2Corridor.energy α c).toReal := by
        dsimp [κ, rateCoefficient]
        ring
      simpa [htarget] using hneg.congr' heq.symm
    exact ⟨hnull, hpositive, hratio⟩

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
    have hpieces := fun i : Fin C₃.count => hM2rate (C₃.pieces i)
    have h := tendsto_log_m3_preimage_probability_ratio_of_nullMeasurable
      (iidSequenceLaw ν) C₃ paths denominator hdenom hκ
      (fun n i => (hpieces i).1 n)
      (fun i => (hpieces i).2.1)
      (fun i => by
        simpa [M3.hAlpha] using (hpieces i).2.2)
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

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

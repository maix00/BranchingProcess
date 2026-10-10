/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PartitionLimit
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Rate
public import Probability.Process.RandomWalk.Path.Skorokhod
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.Approximation
public import Probability.Process.Stable.SmallDeviation.PathClass.StepCorridor.Rate

/-!
# From the discrete `M₂` estimate to Mogul'skii's path class `M`

The exact finite-partition estimate is the discrete Lemma 3 input.  This file
converts its normalization to the common negative denominator and feeds all
`M₂` corridor rates into the existing `M₃` and `M` approximation arguments.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor

/-- The logarithmic denominator matching the discrete small-deviation rate.
It tends to `-∞` when the stable scales satisfy Mogul'skii's two-scale
condition. -/
noncomputable def probabilityRateDenominator
    (α : ℝ) (ν : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℝ :=
  -((stableSmallDeviationRate α ν scale n)⁻¹)

theorem stableSmallDeviationRate_pos_eventually
    {α : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν)) :
    ∀ᶠ n : ℕ in atTop, 0 < stableSmallDeviationRate α ν scale n := by
  have hslowPos : ∀ᶠ n : ℕ in atTop,
      0 < stableSlowVariation α ν (scale n) :=
    hscale.scale_tendsto_atTop.eventually hslow.eventually_pos
  filter_upwards [eventually_gt_atTop (0 : ℕ), hscale.eventually_scale_pos,
    hslowPos] with n hn hs hL
  rw [stableSmallDeviationRate]
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  positivity

/-- Reversing the sign of the internal negative rate denominator gives the
source normalization `n * L*(aₙ) / aₙ^α` and reverses the limiting coefficient.
This is the normalization in Mogul'skii's random-walk theorem. -/
theorem tendsto_log_div_stableRateNormalization_of_neg
    {ν : Measure ℝ} {α : ℝ} {scale : ℕ → ℝ}
    {x : ℕ → ℝ} {L : ℝ}
    (hrate : ∀ᶠ n : ℕ in atTop,
      0 < stableSmallDeviationRate α ν scale n)
    (h : Tendsto
      (fun n : ℕ => x n / probabilityRateDenominator α ν scale n)
      atTop (𝓝 L)) :
    Tendsto
      (fun n : ℕ => x n / stableRateNormalization α ν scale n)
      atTop (𝓝 (-L)) := by
  have heq : (fun n : ℕ => x n / stableRateNormalization α ν scale n) =ᶠ[atTop]
      fun n => -(x n / probabilityRateDenominator α ν scale n) := by
    filter_upwards [hrate] with n hn
    have hn' : stableSmallDeviationRate α ν scale n ≠ 0 := hn.ne'
    simp only [stableRateNormalization, probabilityRateDenominator]
    field_simp [hn']
  exact h.neg.congr' heq.symm

/-- The converse normalization conversion, used to transport uniqueness from
the internal negative-denominator statement to the source normalization. -/
theorem tendsto_log_div_probabilityRateDenominator_of_stableRateNormalization
    {ν : Measure ℝ} {α : ℝ} {scale : ℕ → ℝ}
    {x : ℕ → ℝ} {L : ℝ}
    (hrate : ∀ᶠ n : ℕ in atTop,
      0 < stableSmallDeviationRate α ν scale n)
    (h : Tendsto
      (fun n : ℕ => x n / stableRateNormalization α ν scale n)
      atTop (𝓝 L)) :
    Tendsto
      (fun n : ℕ => x n / probabilityRateDenominator α ν scale n)
      atTop (𝓝 (-L)) := by
  have heq : (fun n : ℕ => x n / probabilityRateDenominator α ν scale n) =ᶠ[atTop]
      fun n => -(x n / stableRateNormalization α ν scale n) := by
    filter_upwards [hrate] with n hn
    have hn' : stableSmallDeviationRate α ν scale n ≠ 0 := hn.ne'
    simp only [stableRateNormalization, probabilityRateDenominator]
    field_simp [hn']
  exact h.neg.congr' heq.symm

private theorem probabilityRateDenominator_tendsto_atBot
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

/-- The discrete exact `M₂` rates imply Mogul'skii's theorem for every
null-measurable path set in the source class `M`.  The hypotheses before
`hG` are precisely the stable-process escape estimate, attraction input, and
functional tightness needed by the discrete Lemma 3 estimate. -/
theorem tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_discretestepCorridorRates
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
    (hGnull : ∀ n : ℕ,
      NullMeasurableSet
        {increment : ℕ → ℝ |
          RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}
        (iidSequenceLaw ν)) :
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
            probabilityRateDenominator α ν scale n)
        atTop (𝓝 (rateCoefficient α C * H)) := by
  let paths : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ := fun n increment =>
    RandomWalk.normalizedStepCadlagPathIcc scale n increment
  let denominator : ℕ → ℝ := probabilityRateDenominator α ν scale
  let rate : ℕ → ℝ := stableSmallDeviationRate α ν scale
  let κ : ℝ := rateCoefficient α C
  have hκ : 0 < κ := by
    exact rateCoefficient_pos hEscape.negative
  have hdenom : Tendsto denominator atTop atBot := by
    simpa [denominator] using probabilityRateDenominator_tendsto_atBot
      hscale hα hα₂ hslow
  have hratePos : ∀ᶠ n : ℕ in atTop, 0 < rate n :=
    stableSmallDeviationRate_pos_eventually hscale hslow
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
    have hdiscrete := tendsto_scaledLog_normalizedStepCorridor_eq_energyRate
      hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase c
    have hEvent (n : ℕ) :
        {increment : ℕ → ℝ | paths n increment ∈ c.toSet} =
          {increment : ℕ → ℝ |
            RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
              corridorSet c.upper c.lower} := by
      ext increment
      simp [paths, ContinuousAdmissibleStepCorridor.toSet, FiniteStepCorridor.toSet]
    have hfiniteProbability (n : ℕ) :
        iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ c.toSet} ≠ ⊤ :=
      measure_ne_top _ _
    have hnull : ∀ n : ℕ, NullMeasurableSet
        {increment : ℕ → ℝ | paths n increment ∈ c.toSet}
        (iidSequenceLaw ν) := by
      intro n
      exact ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability.ContinuousAdmissibleStepCorridor.nullMeasurableSet_preimage_toSet_of_aemeasurable
        c (iidSequenceLaw ν) (paths n) (by
          dsimp [paths]
          exact RandomWalk.measurable_normalizedStepCadlagPathIcc scale n
        |>.aemeasurable)
    have hpositive : ∀ᶠ n : ℕ in atTop,
        0 < (iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal := by
      filter_upwards [hdiscrete.1] with n hn
      rw [hEvent n]
      exact ENNReal.toReal_pos (ne_of_gt hn) (measure_ne_top _ _)
    have hlograte : Tendsto (fun n : ℕ => rate n * Real.log
        (iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal)
        atTop (𝓝 (C * 2 ^ α * (ContinuousAdmissibleStepCorridor.energy α c).toReal)) := by
      have h := hdiscrete.2
      have heq : (fun n : ℕ => rate n * Real.log
          (iidSequenceLaw ν
            {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) =ᶠ[atTop]
          (fun n : ℕ => stableSmallDeviationRate α ν scale n * Real.log
            (iidSequenceLaw ν
              {increment : ℕ → ℝ |
                RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
                  corridorSet c.upper c.lower}).toReal) := by
        filter_upwards [] with n
        simp [rate, hEvent n]
      exact h.congr' heq
    have hratio : Tendsto (fun n : ℕ => Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) /
            denominator n)
        atTop (𝓝 (κ * (ContinuousAdmissibleStepCorridor.energy α c).toReal)) := by
      have heq : (fun n : ℕ => Real.log
          ((iidSequenceLaw ν
            {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal) /
              denominator n) =ᶠ[atTop]
          (fun n : ℕ => -(rate n * Real.log
            (iidSequenceLaw ν
              {increment : ℕ → ℝ | paths n increment ∈ c.toSet}).toReal)) := by
        filter_upwards [hratePos] with n hrate
        have hrateNe : rate n ≠ 0 := hrate.ne'
        dsimp [denominator, probabilityRateDenominator, rate]
        field_simp [hrateNe]
      have hneg := hlograte.neg
      have htarget : -(C * 2 ^ α * (ContinuousAdmissibleStepCorridor.energy α c).toReal) =
          κ * (ContinuousAdmissibleStepCorridor.energy α c).toReal := by
        dsimp [κ, rateCoefficient]
        ring
      simpa [htarget] using hneg.congr' heq.symm
    exact ⟨hnull, hpositive, hratio⟩
  exact tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_stepCorridorRates
    (iidSequenceLaw ν) paths denominator hdenom hκ hG hGnull hStepCorridorRate

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

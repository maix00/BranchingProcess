/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Realization
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourcePathClassRate
import Probability.Process.Stable.Levy
import Probability.Process.Stable.PathLaw.UnitInterval

/-!
# Stable-domain rates under arbitrary i.i.d. realizations

This is the stable random-walk specialization of the generic realization
transfer. It derives each finite-corridor rate from the source-path
Mogul'skii estimate, so callers provide the process and domain-of-attraction
inputs instead of a separate finite-union rate family.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

/-- The source-path stable Mogul'skii inner/outer rate for any realization of
an i.i.d. sequence. The finite-union rates required by the abstract
realization theorem are derived internally from the source corridor theorem.
No measurability assumption on the target path set is needed. -/
theorem existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_iid_of_sourceStableInputs
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    {XΩ : Type*} [MeasurableSpace XΩ]
    {X : ℝ≥0 → XΩ → ℝ} {Q : Measure XΩ} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    {coordinate : ℕ → Ω → ℝ}
    (hindep : iIndepFun coordinate P)
    (hmeasurable : ∀ k, Measurable (coordinate k))
    (hlaw : ∀ k, HasLaw (coordinate k) ν P)
    {G : Set (CadlagPath unitInterval ℝ)}
    (hG : HasVanishingEnergyGapApproximation α G) :
    ∃ C, HasStableProcessEscapeRate α μ
        (hX.unitIntervalPathLaw : Measure (CadlagPath unitInterval ℝ)) C ∧
      ∃! H : ℝ,
        ∃ A : FiniteCorridorUnionApproximation α G,
          ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
            H = hLimits.commonEnergy ∧
            (∀ᶠ n : ℕ in atTop,
              0 < ((P.innerMeasure {ω |
                RandomWalk.sourceNormalizedStepCadlagPathIcc scale n
                  (fun k => coordinate k ω) ∈ G}).toReal)) ∧
            (∀ᶠ n : ℕ in atTop,
              0 < (P {ω |
                RandomWalk.sourceNormalizedStepCadlagPathIcc scale n
                  (fun k => coordinate k ω) ∈ G}).toReal) ∧
            0 < H ∧ H ≤ FiniteCorridorUnion.realEnergy (A.inner 0) ∧
            Tendsto (fun n : ℕ => Real.log
              ((P.innerMeasure {ω |
                RandomWalk.sourceNormalizedStepCadlagPathIcc scale n
                  (fun k => coordinate k ω) ∈ G}).toReal) /
                  probabilityRateDenominator α ν scale n)
              atTop (𝓝 (rateCoefficient α C * H)) ∧
            Tendsto (fun n : ℕ => Real.log
              ((P {ω |
                RandomWalk.sourceNormalizedStepCadlagPathIcc scale n
                  (fun k => coordinate k ω) ∈ G}).toReal) /
                  probabilityRateDenominator α ν scale n)
              atTop (𝓝 (rateCoefficient α C * H)) := by
  obtain ⟨C, hEscape⟩ :=
    hX.isStableClockProcessLaw_unitIntervalPathLaw
      |>.hasStableProcessEscapeRate_of_isStableLevyProcess hX hcdf
  let paths : ℕ → Ω → CadlagPath unitInterval ℝ := fun n ω =>
    RandomWalk.sourceNormalizedStepCadlagPathIcc scale n (fun k => coordinate k ω)
  let denominator : ℕ → ℝ := probabilityRateDenominator α ν scale
  let κ : ℝ := rateCoefficient α C
  have hκ : 0 < κ := rateCoefficient_pos hEscape.negative
  have hdenom : Tendsto denominator atTop atBot := by
    simpa [denominator] using sourceProbabilityRateDenominator_tendsto_atBot
      hscale hα hα₂ hslow
  have hStepCorridorRate : ∀ c : ContinuousAdmissibleStepCorridor,
      (∀ n : ℕ, NullMeasurableSet
        {increment : ℕ → ℝ |
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ c.toSet}
        (iidSequenceLaw ν)) ∧
      (∀ᶠ n : ℕ in atTop,
        0 < (iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ c.toSet}).toReal) ∧
      Tendsto (fun n : ℕ => Real.log
        (iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ c.toSet}).toReal /
              denominator n)
        atTop (𝓝 (κ * (c.energy α).toReal)) := by
    intro c
    simpa [denominator, κ] using
      sourceNormalizedStepCorridor_admissibleStepCorridor_rate
        hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase c
  have hFiniteUnionRate : ∀ C₃ : FiniteCorridorUnion α,
      (∀ᶠ n : ℕ in atTop,
        0 < (iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ C₃.toSet}).toReal) ∧
      Tendsto (fun n : ℕ => Real.log
        (iidSequenceLaw ν
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ C₃.toSet}).toReal /
              denominator n)
        atTop (𝓝 (κ * C₃.realEnergy)) := by
    intro C₃
    let hpieces := fun i : Fin C₃.count => hStepCorridorRate (C₃.pieces i)
    have h := tendsto_log_finiteCorridorUnion_preimage_probability_ratio_of_nullMeasurable
      (iidSequenceLaw ν) C₃
      (fun n increment => RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment)
      denominator hdenom hκ
      (fun n i => (hpieces i).1 n)
      (fun i => (hpieces i).2.1)
      (fun i => by simpa [FiniteCorridorUnion.realEnergy] using (hpieces i).2.2)
    exact ⟨h.2.1, h.2.2⟩
  refine ⟨C, hEscape, ?_⟩
  exact existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_iid
    P hdenom hκ hindep hmeasurable hlaw scale hFiniteUnionRate hG

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

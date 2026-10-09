/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.SourcePath
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourcePathClassRate
import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.Relative

/-!
# Relative path-class rates for source-convention random walks

The source path law is supported on the terminal-left path space. This module
uses that support to transfer the finite-corridor rates to a target that is
approximable by `M₃` corridors only relative to that path space.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open Skorokhod
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor

/-- Every relatively `M` set in the source terminal-left path space has a
unique common logarithmic rate for its inner and outer probabilities along the
source-normalized random walk. No measurability assumption on the target set
is needed. -/
theorem existsUnique_inner_outer_log_probability_ratio_of_hasRelativeVanishingEnergyGapApproximation_of_sourceDiscretestepCorridorRates
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
    {G : Set (CadlagPath unitInterval ℝ)}
    (hG : HasRelativeVanishingEnergyGapApproximation α terminalLeftPathSpace G) :
    ∃! H : ℝ,
      ∃ A : RelativeFiniteCorridorUnionApproximation α terminalLeftPathSpace G,
        ∃ hLimits : RelativeFiniteCorridorUnionEnergyLimits A,
          H = hLimits.commonEnergy ∧
          (∀ᶠ n : ℕ in atTop,
            0 < ((iidSequenceLaw ν).innerMeasure
              {increment : ℕ → ℝ |
                RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
          (∀ᶠ n : ℕ in atTop,
            0 < (iidSequenceLaw ν
              {increment : ℕ → ℝ |
                RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
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
  have hpaths : ∀ n increment, paths n increment ∈ terminalLeftPathSpace := by
    intro n increment
    exact terminalLeftPath_mem_space
      (RandomWalk.normalizedStepCadlagPathIcc scale n increment)
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
  obtain ⟨H, hH, hUnique⟩ :=
    existsUnique_inner_outer_log_probability_ratio_of_hasRelativeVanishingEnergyGapApproximation
      (iidSequenceLaw ν) paths terminalLeftPathSpace hpaths denominator hdenom hκ hG hFiniteUnionRate
  refine ⟨H, ?_, hUnique⟩
  obtain ⟨A, hLimits, rfl, hInnerPos, hOuterPos, hInnerRate, hOuterRate⟩ := hH
  refine ⟨A, hLimits, rfl, hInnerPos, hOuterPos, ?_, ?_⟩
  · simpa [paths, denominator, κ] using hInnerRate
  · simpa [paths, denominator, κ] using hOuterRate

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

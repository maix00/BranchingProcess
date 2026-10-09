/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourceOnly.ContinuousBoundary
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourceOnly.Realization

/-!
# Continuous-boundary rates for arbitrary i.i.d. realizations

The raw-source continuous-corridor theorem is first proved for the canonical
i.i.d. sequence law. This module transfers it to any independent measurable
sequence with the same one-coordinate law, using the measurable finite-step
corridor preimage. No path-space measurability assumption is added.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor

/-- The source continuous-boundary rate for an arbitrary i.i.d. realization.
The proof transfers the canonical-sequence result through the measurable
preimage event, and therefore retains exactly the raw stable-domain
assumptions. -/
theorem exists_source_continuousBoundary_probability_rate_of_rawSource_of_iid
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable α μ)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hcenter : α ≠ 1 ∨ IsMogulskiiIndexOneCentered ν normalization)
    {coordinate : ℕ → Ω → ℝ}
    (hindep : iIndepFun coordinate P)
    (hmeasurable : ∀ k, Measurable (coordinate k))
    (hlaw : ∀ k, HasLaw (coordinate k) ν P)
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    ∃ d Csource : ℝ,
      0 < d ∧ Csource < 0 ∧
      (∀ᶠ n : ℕ in atTop,
        0 < (P {ω | sourceNormalizedStepCadlagPathIcc scale n
          (fun k => coordinate k ω) ∈
            relativeContinuousBoundaryCorridorSet lower upper}).toReal) ∧
      Tendsto
        (fun n : ℕ => Real.log
          (P {ω | sourceNormalizedStepCadlagPathIcc scale n
            (fun k => coordinate k ω) ∈
              relativeContinuousBoundaryCorridorSet lower upper}).toReal /
            probabilityRateDenominator α ν scale n)
        atTop (𝓝 (rateCoefficient α (d * Csource) *
          ∫ t : unitInterval, continuousBoundaryDensity α lower upper t ∂volume)) := by
  obtain ⟨d, Csource, hd, hCsource, hpositive, hrate⟩ :=
    exists_source_continuousBoundary_probability_rate_of_rawSource
      hsmall hStable hDOA hcdf hα₀ hα₂ hcenter lower upper hwidth
      hstartLower hstartUpper
  have hsequence : HasLaw (fun ω k => coordinate k ω)
      (iidSequenceLaw ν) P := hindep.hasLaw_iidSequenceLaw hmeasurable hlaw
  have hprobabilityEq (n : ℕ) :
      P {ω | sourceNormalizedStepCadlagPathIcc scale n
          (fun k => coordinate k ω) ∈
            relativeContinuousBoundaryCorridorSet lower upper} =
        iidSequenceLaw ν {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale n increment ∈
            relativeContinuousBoundaryCorridorSet lower upper} := by
    exact hsequence.measure_eq
      (measurableSet_sourceNormalizedStepCadlagPathIcc_preimage_relativeContinuousBoundaryCorridorSet
        lower upper scale n)
  have hpositive' : ∀ᶠ n : ℕ in atTop,
      0 < (P {ω | sourceNormalizedStepCadlagPathIcc scale n
        (fun k => coordinate k ω) ∈
          relativeContinuousBoundaryCorridorSet lower upper}).toReal := by
    filter_upwards [hpositive] with n hn
    rw [hprobabilityEq n]
    exact hn
  have heq :
      (fun n : ℕ => Real.log
        (P {ω | sourceNormalizedStepCadlagPathIcc scale n
          (fun k => coordinate k ω) ∈
            relativeContinuousBoundaryCorridorSet lower upper}).toReal /
          probabilityRateDenominator α ν scale n) =ᶠ[atTop]
      (fun n : ℕ => Real.log
        (iidSequenceLaw ν {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale n increment ∈
            relativeContinuousBoundaryCorridorSet lower upper}).toReal /
          probabilityRateDenominator α ν scale n) := by
    filter_upwards [] with n
    rw [hprobabilityEq n]
  exact ⟨d, Csource, hd, hCsource, hpositive', hrate.congr' heq.symm⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

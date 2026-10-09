/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Moments.Truncated
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Gaussian.SourcePathClass

/-!
# Finite-variance specialization of the normal-domain Mogul'skii rate

The normal-domain theorem allows infinite variance.  When the second moment is
finite, the truncated second moment tends to the variance, giving the familiar
variance-scaled exponent as a direct consequence.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian

open Skorokhod.PathClass.StepCorridor
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- For finite-variance increments in the normal domain, the source-path
Mogul'skii rate has the usual variance factor.  The underlying normal-domain
theorem remains applicable without this finite-moment assumption. -/
theorem tendsto_scaledLog_sourceProbability_of_finiteVariance
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale 2 ν normalization scale)
    (hDOA : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization (fun _ => 0))
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B Q)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation 2 G)
    (hGmeas : MeasurableSet G)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x : ℝ, x ^ 2 ∂ν) :
    ∃ H : ℝ, ∃ A : FiniteCorridorUnionApproximation 2 G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
      H = hLimits.commonEnergy ∧
      Tendsto
        (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
          ((iidSequenceLaw ν {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal))
        atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x : ℝ, x ^ 2 ∂ν) * hLimits.commonEnergy)) := by
  obtain ⟨_, ⟨_, ⟨H, hRateData, _hUnique⟩⟩⟩ :=
    tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_source_index_two_of_brownian_explicit
      hscale hDOA hB hG hGmeas
  rcases hRateData with ⟨⟨A, hLimits, hH⟩, hRate⟩
  subst H
  have htruncated := tendsto_truncatedSecondMoment ν hsquare
  have hvarianceLimit : Tendsto
      (fun n : ℕ => stableSlowVariation 2 ν (scale n)) atTop
      (𝓝 (∫ x : ℝ, x ^ 2 ∂ν)) := by
    have h := htruncated.comp hscale.scale_tendsto_atTop
    convert h using 1
    funext n
    exact stableSlowVariation_two ν (scale n)
  have hratePos : ∀ᶠ n : ℕ in atTop,
      0 < stableRateNormalization 2 ν scale n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hscale.eventually_scale_pos,
      hvarianceLimit.eventually (Ioi_mem_nhds hvariance)] with n hn hscaleN hL
    rw [stableRateNormalization_eq]
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
    have hscaleSq : 0 < (scale n) ^ (2 : ℝ) := Real.rpow_pos_of_pos hscaleN _
    exact div_pos (mul_pos hnReal hL) hscaleSq
  have hlogRate : Tendsto
      (fun n : ℕ => Real.log
        ((iidSequenceLaw ν {increment : ℕ → ℝ |
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
          stableRateNormalization 2 ν scale n)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * hLimits.commonEnergy)) := hRate
  have hproduct := hlogRate.mul hvarianceLimit
  have hfinal : Tendsto
      (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
        ((iidSequenceLaw ν {increment : ℕ → ℝ |
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal))
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x : ℝ, x ^ 2 ∂ν) * hLimits.commonEnergy)) := by
    have hEq : (fun n : ℕ =>
        Real.log ((iidSequenceLaw ν {increment : ℕ → ℝ |
          RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
          stableRateNormalization 2 ν scale n * stableSlowVariation 2 ν (scale n)) =ᶠ[atTop]
        (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
          ((iidSequenceLaw ν {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal)) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ), hscale.eventually_scale_pos,
        hvarianceLimit.eventually (Ioi_mem_nhds hvariance)] with n hn hscaleN hL
      rw [stableRateNormalization_eq, stableSlowVariation_two]
      have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hL' : 0 < truncatedSecondMoment ν (scale n) := by
        simpa using hL
      have hLne : truncatedSecondMoment ν (scale n) ≠ 0 := ne_of_gt hL'
      rw [Real.rpow_two]
      field_simp [hnReal, hLne]
    have hlimit := hproduct.congr' hEq
    convert hlimit using 1
    ring_nf
  exact ⟨hLimits.commonEnergy, A, hLimits, rfl, hfinal⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian

end

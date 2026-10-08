/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Tightness.Skorokhod
public import Probability.Process.RandomWalk.FunctionalLimit.OscillationPartitions
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.Centering
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.Oscillation
public import Probability.Process.RandomWalk.Path.Skorokhod
public import Topology.Cadlag.Skorokhod.Oscillation.DoubleExcursion.Converse

/-!
# Stable random-walk oscillation partitions

This module combines the stable block-tail excursion estimates with the
general Skorokhod partition criterion. It constructs the multiscale event and
its probability bounds; compact-range control and tightness are handled in
the sibling `Tightness` module.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

/-- Stable-domain block estimates are adapted to the distribution-independent
oscillation-partition construction. The source-dependent work is limited to
control of the truncation bias and the two local failure probabilities. -/
theorem exists_eventually_oscillationPartitions_bound_of_stableNorming
    {α radiusMultiplier : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hradius : 0 < radiusMultiplier)
    (biasBound : ℝ) (hbiasBound : 0 ≤ biasBound)
    (hbiasProvider : ∀ {thresholdMultiplier δ : ℝ} {length : ℕ → ℕ},
      0 < thresholdMultiplier → 0 < δ →
      δ * biasBound < thresholdMultiplier / 2 →
      (∀ᶠ n : ℕ in atTop, (length n : ℝ) / n ≤ δ) →
      ∀ᶠ n : ℕ in atTop,
        (length n : ℝ) *
          |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
            normalization n ≤ thresholdMultiplier / 2)
    {η : ℝ≥0∞} (hη : 0 < η) (hηone : η < 1) :
    ∃ gap oscillationTolerance : ℕ → ℝ,
      (∀ m, 0 < gap m) ∧ (∀ m, 0 < oscillationTolerance m) ∧
        Tendsto oscillationTolerance atTop (nhds 0) ∧
          ∀ᶠ n : ℕ in atTop,
            (normalizedStepPathLaw ν normalization n)
              (Skorokhod.admitsOscillationPartitionSequence
                (E := ℝ) gap oscillationTolerance)ᶜ ≤ η := by
  let coefficient : ℝ → ℝ := fun ε =>
    ((2 - α) / α) * radiusMultiplier ^ (-α) + 1 +
      4 * (radiusMultiplier ^ (2 - α) + 1) / (ε / 2) ^ 2
  have hcoefficient : ∀ {ε : ℝ}, 0 < ε → 0 < coefficient ε := by
    intro ε hε
    dsimp [coefficient]
    positivity
  have hscale : ∀ᶠ n : ℕ in atTop, 0 < normalization n :=
    hnorm.2.1.eventually (eventually_gt_atTop 0)
  apply ProbabilityTheory.RandomWalk.FunctionalLimit.exists_eventually_oscillationPartitions_bound_of_localEstimates
    hscale coefficient hcoefficient biasBound hbiasBound
  · intro ε endpointDelta blockFraction width hε hEndpoint hBlock hsmall hwidth hwidthLower hratio
    have hsmall' : blockFraction * biasBound < (ε / 2) / 2 := by
      simpa [show (ε / 2) / 2 = ε / 4 by ring] using hsmall
    have hratio' : ∀ᶠ n : ℕ in atTop,
        ((fun n : ℕ => 2 * width n) n : ℝ) / n ≤ blockFraction := by
      filter_upwards [hratio] with n hn
      simpa using hn
    have hbias := hbiasProvider
      (thresholdMultiplier := ε / 2) (δ := blockFraction)
      (length := fun n => 2 * width n)
      (by positivity) hBlock hsmall' hratio'
    have hbias' : ∀ᶠ n : ℕ in atTop,
        (2 * width n : ℝ) *
          |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
            normalization n ≤ ε / 4 := by
      filter_upwards [hbias] with n hn
      simpa [Nat.cast_mul, show (ε / 2) / 2 = ε / 4 by ring] using hn
    have hdouble := eventually_measure_not_hasDoubleExcursionBound_le_of_stableNorming
      (endpointDelta := endpointDelta) (blockFraction := blockFraction)
      hnorm hα₀ hα₂ htail hradius hε hBlock.le width hwidth hwidthLower hratio hbias'
    simpa [coefficient] using hdouble
  · intro ε endpointDelta blockFraction width hε hEndpoint hBlock hsmall hwidth hwidthLower hratio
    have hsmall' : blockFraction * biasBound < (ε / 2) / 2 := by
      simpa [show (ε / 2) / 2 = ε / 4 by ring] using hsmall
    have hbias := hbiasProvider
      (thresholdMultiplier := ε / 2) (δ := blockFraction)
      (length := width)
      (by positivity) hBlock hsmall' hratio
    have hbias' : ∀ᶠ n : ℕ in atTop,
        (width n : ℝ) *
          |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
            normalization n ≤ ε / 4 := by
      filter_upwards [hbias] with n hn
      simpa [show (ε / 2) / 2 = ε / 4 by ring] using hn
    have hendpoint := eventually_measure_not_hasEndpointOscillationBound_le_of_stableNorming
      (endpointDelta := endpointDelta) (blockFraction := blockFraction)
      hnorm hα₀ hα₂ htail hradius hε hBlock.le width hwidth hwidthLower hratio hbias'
    simpa [coefficient] using hendpoint
  · exact hη
  · exact hηone

/-- Below stable index one, the uncentered source convention supplies the
truncation-bias input needed for the stable oscillation-partition estimate. -/
theorem exists_eventually_oscillationPartitions_bound_of_index_lt_one
    {α : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    {η : ℝ≥0∞} (hη : 0 < η) (hηone : η < 1) :
    ∃ gap oscillationTolerance : ℕ → ℝ,
      (∀ m, 0 < gap m) ∧ (∀ m, 0 < oscillationTolerance m) ∧
        Tendsto oscillationTolerance atTop (nhds 0) ∧
          ∀ᶠ n : ℕ in atTop,
            (normalizedStepPathLaw ν normalization n)
              (Skorokhod.admitsOscillationPartitionSequence
                (E := ℝ) gap oscillationTolerance)ᶜ ≤ η := by
  let biasBound : ℝ := truncationBiasConstant α 1
  have hbiasBound : 0 ≤ biasBound := by
    dsimp [biasBound, truncationBiasConstant]
    rw [Real.one_rpow]
    have hαden : 0 < 1 - α := by linarith
    have hαnum : 0 < 2 - α := by linarith
    positivity
  apply exists_eventually_oscillationPartitions_bound_of_stableNorming
    hnorm hα₀ (by linarith) htail (by norm_num : 0 < (1 : ℝ))
    biasBound hbiasBound
  · intro thresholdMultiplier δ length hthreshold hδ hsmall hlength
    have hsmall' : δ * truncationBiasConstant α 1 < thresholdMultiplier / 2 := by
      simpa [biasBound] using hsmall
    exact eventually_truncatedIncrementBias_le_of_stableNorming_of_index_lt_one
      hnorm hα₀ hα₁ htail (by norm_num : 0 < (1 : ℝ)) hδ hsmall' hlength
  · exact hη
  · exact hηone

/-- At stable index one, Mogulskii's sine-centering condition supplies the
truncation-bias input needed for the stable oscillation-partition estimate. -/
theorem exists_eventually_oscillationPartitions_bound_of_index_one
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming 1 ν normalization)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-1))
    (hcenter : IsMogulskiiIndexOneCentered ν normalization)
    {η : ℝ≥0∞} (hη : 0 < η) (hηone : η < 1) :
    ∃ gap oscillationTolerance : ℕ → ℝ,
      (∀ m, 0 < gap m) ∧ (∀ m, 0 < oscillationTolerance m) ∧
        Tendsto oscillationTolerance atTop (nhds 0) ∧
          ∀ᶠ n : ℕ in atTop,
            (normalizedStepPathLaw ν normalization n)
              (Skorokhod.admitsOscillationPartitionSequence
                (E := ℝ) gap oscillationTolerance)ᶜ ≤ η := by
  let biasBound : ℝ := indexOneTruncationBiasConstant 1
  have hbiasBound : 0 ≤ biasBound := by
    dsimp [biasBound, indexOneTruncationBiasConstant]
    norm_num
  apply exists_eventually_oscillationPartitions_bound_of_stableNorming
    hnorm (by norm_num) (by norm_num) htail (by norm_num : 0 < (1 : ℝ))
    biasBound hbiasBound
  · intro thresholdMultiplier δ length hthreshold hδ hsmall hlength
    have hsmall' : δ * indexOneTruncationBiasConstant 1 <
        thresholdMultiplier / 2 := by
      simpa [biasBound] using hsmall
    exact eventually_truncatedIncrementBias_le_of_stableNorming_of_index_one
      hnorm htail (by norm_num : 0 < (1 : ℝ)) hcenter hδ hsmall' hlength
  · exact hη
  · exact hηone

/-- Above stable index one, integrable centered increments supply the
truncation-bias input needed for the stable oscillation-partition estimate. -/
theorem exists_eventually_oscillationPartitions_bound_of_index_gt_one
    {α : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : 1 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hint : Integrable (fun x : ℝ => x) ν)
    (hcenter : (∫ x : ℝ, x ∂ν) = 0)
    {η : ℝ≥0∞} (hη : 0 < η) (hηone : η < 1) :
    ∃ gap oscillationTolerance : ℕ → ℝ,
      (∀ m, 0 < gap m) ∧ (∀ m, 0 < oscillationTolerance m) ∧
        Tendsto oscillationTolerance atTop (nhds 0) ∧
          ∀ᶠ n : ℕ in atTop,
            (normalizedStepPathLaw ν normalization n)
              (Skorokhod.admitsOscillationPartitionSequence
                (E := ℝ) gap oscillationTolerance)ᶜ ≤ η := by
  let biasBound : ℝ := discardedTailBiasConstant α 1
  have hbiasBound : 0 ≤ biasBound := by
    dsimp [biasBound, discardedTailBiasConstant]
    rw [Real.one_rpow]
    positivity
  apply exists_eventually_oscillationPartitions_bound_of_stableNorming
    hnorm hα₀ hα₂ htail (by norm_num : 0 < (1 : ℝ))
    biasBound hbiasBound
  · intro thresholdMultiplier δ length hthreshold hδ hsmall hlength
    have hsmall' : δ * discardedTailBiasConstant α 1 <
        thresholdMultiplier / 2 := by
      simpa [biasBound] using hsmall
    exact eventually_truncatedIncrementBias_le_of_stableNorming_of_index_gt_one
      hnorm hα₀ hα₁ hα₂ htail (by norm_num : 0 < (1 : ℝ))
      hint hcenter hδ hsmall' hlength
  · exact hη
  · exact hηone

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end

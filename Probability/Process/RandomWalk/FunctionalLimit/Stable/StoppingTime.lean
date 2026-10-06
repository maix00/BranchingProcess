/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Stable.BlockTail
public import Probability.Process.RandomWalk.Path.Block.Law.StoppingTime

/-!
# Stable block bounds after stopping times

The local stable-domain excursion estimate also holds after any discrete
stopping time in the increment filtration.  This is the random-start form of
the block estimate used as an input to path tightness criteria.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

/-- A stable-domain one-block estimate remains valid when the block starts at
an arbitrary discrete stopping time, possibly depending on the sample size.
The stopping-time extension is obtained by conditioning on each finite value
of the time and using independence of the following increments. -/
theorem eventually_measure_blockPrefixExceedanceAfter_le_of_stableNorming
    {α radiusMultiplier thresholdMultiplier δ : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hradius : 0 < radiusMultiplier) (hthreshold : 0 < thresholdMultiplier)
    (hδ : 0 ≤ δ) (length : ℕ → ℕ)
    (hlength : ∀ᶠ n in atTop, 0 < length n)
    (hlengthRatio : ∀ᶠ n in atTop, (length n : ℝ) / n ≤ δ)
    (hbias : ∀ᶠ n in atTop,
      (length n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
          normalization n ≤ thresholdMultiplier / 2)
    (τ : ℕ → (ℕ → ℝ) → WithTop ℕ)
    (hτ : ∀ n, IsStoppingTime (incrementFiltration (E := ℝ)) (τ n)) :
    ∀ᶠ n in atTop,
      (iidSequenceLaw ν)
          (blockPrefixExceedanceAfter (τ n) (length n)
            (thresholdMultiplier * normalization n)) ≤
        ENNReal.ofReal
          (δ * (((2 - α) / α) * radiusMultiplier ^ (-α) + 1 +
            4 * (radiusMultiplier ^ (2 - α) + 1) / thresholdMultiplier ^ 2)) := by
  filter_upwards [eventually_measure_blockPrefixExceedance_le_of_stableNorming_unitMargins
    hnorm hα₀ hα₂ htail hradius hthreshold hδ length hlength hlengthRatio hbias]
      with n hn
  exact (measure_blockPrefixExceedanceAfter_le ν (τ n) (hτ n)
      (length n) (thresholdMultiplier * normalization n)).trans hn

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end

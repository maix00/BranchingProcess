/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.RegularVariation.Integral
public import Probability.Distributions.Stable.Attraction.Norming.Tail
public import Probability.Process.RandomWalk.Path.Truncation.Moment

/-!
# Truncation bias below the stable index one

For `0 < α < 1`, the uncentered stable-domain convention is compatible with
hard truncation: its mean is bounded by a capped first moment, whose tail
integral is controlled by Karamata's theorem. The index-one centering
convention is intentionally left as a separate input.
-/

open Filter MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

/-- The asymptotic upper bound for the normalized truncation bias when the
one-step law is in a stable domain of index below one. -/
noncomputable def truncationBiasConstant (α radiusMultiplier : ℝ) : ℝ :=
  radiusMultiplier * (((2 - α) / α) * radiusMultiplier ^ (-α)) /
    (1 - α)

/-- The capped absolute first moment at a stable norming radius has the
asymptotic value dictated by the two-sided regularly varying tail. -/
theorem IsStableNorming.tendsto_nat_mul_cappedAbsFirstMoment_div_normalization_of_regularlyVaryingTail
    {α radiusMultiplier : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ}
    (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hradius : 0 < radiusMultiplier) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (∫ x, min |x| (radiusMultiplier * normalization n) ∂ν) /
        normalization n) atTop
      (nhds (truncationBiasConstant α radiusMultiplier)) := by
  let tail : ℝ → ℝ := fun u => ν.real {x : ℝ | u < |x|}
  let cutoff : ℕ → ℝ := fun n => radiusMultiplier * normalization n
  have htailAntitone : Antitone tail := by
    intro u v huv
    apply measureReal_mono (μ := ν)
      (s₁ := {x : ℝ | v < |x|}) (s₂ := {x : ℝ | u < |x|})
    · intro x hx
      exact lt_of_le_of_lt huv hx
  have htailNonneg : ∀ ⦃u : ℝ⦄, 0 ≤ u → 0 ≤ tail u := by
    intro u hu
    exact measureReal_nonneg
  have htailLeOne : ∀ ⦃u : ℝ⦄, 0 ≤ u → tail u ≤ 1 := by
    intro u hu
    exact measureReal_le_one
  have hKaramata := htail.tendsto_intervalIntegral_div_mul_of_antitone
    (le_of_lt hα₀) hα₁ htailAntitone htailNonneg htailLeOne
  have hcutoffTop : Tendsto cutoff atTop atTop := by
    change Tendsto (fun n : ℕ => radiusMultiplier * normalization n) atTop atTop
    exact (tendsto_id.const_mul_atTop hradius).comp hnorm.2.1
  have hKaramataSeq := hKaramata.comp hcutoffTop
  have htailSeq := hnorm.tendsto_nat_mul_twoSidedTail_mul_of_regularlyVarying
    hα₀ (by linarith : α < 2) htail hradius
  have hratioTailMoment : Tendsto (fun n : ℕ =>
      (∫ t in (0 : ℝ)..cutoff n, tail t) /
        (cutoff n * tail (cutoff n))) atTop
      (nhds (1 / (1 - α))) := by
    simpa [Function.comp_def, tail] using hKaramataSeq
  have hproduct := htailSeq.mul hratioTailMoment
  have hcutoffRatio : Tendsto (fun n : ℕ => cutoff n / normalization n)
      atTop (nhds radiusMultiplier) := by
    have heq : (fun n : ℕ => cutoff n / normalization n) =ᶠ[atTop]
        fun _ => radiusMultiplier := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hscale : 0 < normalization n := hnorm.1 n hn
      dsimp [cutoff]
      field_simp [ne_of_gt hscale]
    exact tendsto_const_nhds.congr' heq.symm
  have hlimit := hproduct.mul hcutoffRatio
  have heq : (fun n : ℕ =>
      ((n : ℝ) * tail (cutoff n)) *
        ((∫ t in (0 : ℝ)..cutoff n, tail t) /
          (cutoff n * tail (cutoff n))) *
        (cutoff n / normalization n)) =ᶠ[atTop]
      fun n : ℕ => (n : ℝ) *
        (∫ x, min |x| (cutoff n) ∂ν) / normalization n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      hcutoffTop.eventually htail.eventually_pos] with n hn htailn
    have hscale : 0 < normalization n := hnorm.1 n hn
    have hcutoff : 0 < cutoff n := mul_pos hradius hscale
    have hmoment := integral_min_abs_eq_intervalIntegral_tail ν hcutoff.le
    rw [hmoment]
    dsimp [cutoff, tail]
    field_simp [ne_of_gt hscale, ne_of_gt hcutoff]
    calc
      _ = (∫ t in (0 : ℝ)..(radiusMultiplier * normalization n),
            ν.real {x : ℝ | t < |x|}) *
          (ν.real {x : ℝ | radiusMultiplier * normalization n < |x|} *
            (ν.real {x : ℝ | radiusMultiplier * normalization n < |x|})⁻¹) := by ring
      _ = _ := by
        rw [mul_inv_cancel₀ (ne_of_gt htailn), mul_one]
  have hlimit' := hlimit.congr' heq
  have hconst : (((2 - α) / α) * radiusMultiplier ^ (-α)) *
      (1 / (1 - α)) * radiusMultiplier =
        truncationBiasConstant α radiusMultiplier := by
    simp [truncationBiasConstant, div_eq_mul_inv]
    ring
  rw [hconst] at hlimit'
  exact hlimit'

/-- For `0 < α < 1`, the truncation bias of a block of length at most `δ n`
is eventually below half the excursion threshold whenever `δ` is chosen
below the explicit stable-tail bias scale. No moment condition on the
untruncated increment is used. -/
theorem eventually_truncatedIncrementBias_le_of_stableNorming_of_index_lt_one
    {α radiusMultiplier thresholdMultiplier δ : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hradius : 0 < radiusMultiplier)
    {length : ℕ → ℕ} (δpos : 0 < δ)
    (hsmall : δ * truncationBiasConstant α radiusMultiplier <
      thresholdMultiplier / 2)
    (hlength : ∀ᶠ n in atTop, (length n : ℝ) / n ≤ δ) :
    ∀ᶠ n in atTop,
      (length n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
          normalization n ≤ thresholdMultiplier / 2 := by
  let biasRatio : ℕ → ℝ := fun n => (n : ℝ) *
    (∫ x, min |x| (radiusMultiplier * normalization n) ∂ν) /
      normalization n
  let biasConstant := truncationBiasConstant α radiusMultiplier
  have hbiasLimit := IsStableNorming.tendsto_nat_mul_cappedAbsFirstMoment_div_normalization_of_regularlyVaryingTail
    hnorm hα₀ hα₁ htail hradius
  have hmargin : 0 < thresholdMultiplier / 2 - δ * biasConstant := by
    linarith [hsmall]
  let η : ℝ := (thresholdMultiplier / 2 - δ * biasConstant) / (2 * δ)
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hbound : δ * (biasConstant + η) < thresholdMultiplier / 2 := by
    dsimp [η]
    have hδ : 0 < δ := δpos
    field_simp
    nlinarith
  have hratioEventually : ∀ᶠ n in atTop, biasRatio n < biasConstant + η := by
    have hmem : Set.Iio (biasConstant + η) ∈ nhds biasConstant :=
      Iio_mem_nhds (by dsimp [η]; linarith [hmargin, δpos])
    filter_upwards [hbiasLimit.eventually hmem] with n hn
    simpa [biasRatio, biasConstant] using hn
  filter_upwards [hlength, hratioEventually, eventually_gt_atTop (0 : ℕ)]
    with n hlengthn hratioN hn
  have hscale : 0 < normalization n := hnorm.1 n hn
  have hmeanBound := abs_truncatedIncrementMean_le_integral_min_abs ν
    (le_of_lt (mul_pos hradius hscale))
  have hmeanRatio : (n : ℝ) *
      |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
        normalization n ≤ biasRatio n := by
    dsimp [biasRatio]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmeanBound (by positivity)) hscale.le
  have hratioNonneg : 0 ≤ (length n : ℝ) / n :=
    div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hproduct : (length n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
        normalization n =
      ((length n : ℝ) / n) *
        ((n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
            normalization n) := by
    field_simp
  rw [hproduct]
  calc
    ((length n : ℝ) / n) *
        ((n : ℝ) *
          |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
            normalization n) ≤ δ * biasRatio n := by
      exact mul_le_mul hlengthn hmeanRatio (by positivity) δpos.le
    _ ≤ δ * (biasConstant + η) :=
      mul_le_mul_of_nonneg_left (le_of_lt hratioN) δpos.le
    _ ≤ thresholdMultiplier / 2 := le_of_lt hbound

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end

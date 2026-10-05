/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.RegularVariation.Integral
public import Probability.Distributions.Stable.Attraction.Norming.Tail
public import Probability.Distributions.Moments.Truncated.TailIntegral
public import Probability.Process.RandomWalk.Path.Truncation.Moment

/-!
# Truncation bias below the stable index one

For `0 < α < 1`, the uncentered stable-domain convention is compatible with
hard truncation: its mean is bounded by a capped first moment, whose tail
integral is controlled by Karamata's theorem. The index-one centering
convention is intentionally left as a separate input.
-/

open Filter MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

/-- The asymptotic upper bound for the normalized truncation bias when the
one-step law is in a stable domain of index below one. -/
noncomputable def truncationBiasConstant (α radiusMultiplier : ℝ) : ℝ :=
  radiusMultiplier * (((2 - α) / α) * radiusMultiplier ^ (-α)) /
    (1 - α)

/-- The limiting normalized discarded first moment above a positive cutoff
for a centered stable-domain law with index in `(1, 2)`. -/
noncomputable def discardedTailBiasConstant (α radiusMultiplier : ℝ) : ℝ :=
  ((2 - α) / (α - 1)) * radiusMultiplier ^ (1 - α)

/-- For `1 < α < 2`, regular variation and stable norming identify the
normalized first absolute moment discarded above a fixed multiple of the
norming radius. The layer-cake identity and the upper-tail Karamata theorem
are used directly; no second moment is assumed. -/
theorem IsStableNorming.tendsto_nat_mul_discardedAbsFirstMoment_div_normalization_of_regularlyVaryingTail
    {α radiusMultiplier : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ}
    (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : 1 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hradius : 0 < radiusMultiplier)
    (hint : Integrable (fun x : ℝ => x) ν) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (∫ x, ({y : ℝ | radiusMultiplier * normalization n < |y|}).indicator
        (fun y => |y|) x ∂ν) / normalization n) atTop
      (nhds (discardedTailBiasConstant α radiusMultiplier)) := by
  let tail : ℝ → ℝ := fun u => ν.real {x : ℝ | u < |x|}
  let cutoff : ℕ → ℝ := fun n => radiusMultiplier * normalization n
  have htailAntitone : Antitone tail := by
    intro u v huv
    apply measureReal_mono (μ := ν)
      (s₁ := {x : ℝ | v < |x|}) (s₂ := {x : ℝ | u < |x|})
    · intro x hx
      exact lt_of_le_of_lt huv hx
  have htailNonneg : ∀ u, 0 ≤ tail u := fun _ => measureReal_nonneg
  have hKaramata := htail.tendsto_integral_Ioi_div_mul_of_antitone
    (by linarith : 1 < α) htailAntitone htailNonneg
  have hcutoffTop : Tendsto cutoff atTop atTop := by
    change Tendsto (fun n : ℕ => radiusMultiplier * normalization n) atTop atTop
    exact (tendsto_id.const_mul_atTop hradius).comp hnorm.2.1
  have hKaramataSeq := hKaramata.comp hcutoffTop
  have htailSeq := hnorm.tendsto_nat_mul_twoSidedTail_mul_of_regularlyVarying
    hα₀ hα₂ htail hradius
  have hcutoffTailPos : ∀ᶠ n : ℕ in atTop, 0 < tail (cutoff n) :=
    hcutoffTop.eventually htail.eventually_pos
  have hratioTailMoment : Tendsto (fun n : ℕ =>
      (∫ t in Ioi (cutoff n), tail t) / (cutoff n * tail (cutoff n))) atTop
      (nhds (1 / (α - 1))) := by
    simpa [Function.comp_def, tail] using hKaramataSeq
  have hcutoffRatio : Tendsto (fun n : ℕ => cutoff n / normalization n)
      atTop (nhds radiusMultiplier) := by
    have heq : (fun n : ℕ => cutoff n / normalization n) =ᶠ[atTop]
        fun _ => radiusMultiplier := by
      have hnormPos : ∀ᶠ n : ℕ in atTop, 0 < normalization n :=
        hnorm.2.1.eventually (eventually_gt_atTop 0)
      filter_upwards [hnormPos] with n hscale
      dsimp [cutoff]
      field_simp [ne_of_gt hscale]
    exact tendsto_const_nhds.congr' heq.symm
  have hfactor := htailSeq.mul hcutoffRatio
  have hratioAdd : Tendsto (fun n : ℕ =>
      1 + (∫ t in Ioi (cutoff n), tail t) /
        (cutoff n * tail (cutoff n))) atTop
      (nhds (1 + 1 / (α - 1))) :=
    tendsto_const_nhds.add hratioTailMoment
  have hlimit := hfactor.mul hratioAdd
  have hintAbs : Integrable (fun x : ℝ => |x|) ν := by
    simpa only [Real.norm_eq_abs] using hint.norm
  have heq : (fun n : ℕ =>
      ((n : ℝ) * tail (cutoff n)) * (cutoff n / normalization n) *
        (1 + (∫ t in Ioi (cutoff n), tail t) /
          (cutoff n * tail (cutoff n)))) =ᶠ[atTop]
      fun n : ℕ => (n : ℝ) *
        (∫ x, {y : ℝ | cutoff n < |y|}.indicator (fun y => |y|) x ∂ν) /
          normalization n := by
    have hnormPos : ∀ᶠ n : ℕ in atTop, 0 < normalization n :=
      hnorm.2.1.eventually (eventually_gt_atTop 0)
    filter_upwards [hnormPos, hcutoffTailPos] with n hscale htailn
    have hcutoff : 0 < cutoff n := mul_pos hradius hscale
    have hlayer := integral_indicator_abs_eq_radius_mul_tail_add_tailIntegral
      ν hintAbs hcutoff.le
    have htailNe : tail (cutoff n) ≠ 0 := ne_of_gt htailn
    have htailNe' : ν.real {x : ℝ | cutoff n < |x|} ≠ 0 := by
      simpa [tail] using htailNe
    rw [hlayer]
    dsimp [tail, cutoff]
    field_simp [ne_of_gt hscale, ne_of_gt hcutoff, htailNe']
    have hcancel : ν.real {x : ℝ | radiusMultiplier * normalization n < |x|} *
        (ν.real {x : ℝ | radiusMultiplier * normalization n < |x|})⁻¹ = 1 :=
      mul_inv_cancel₀ htailNe'
    let T := ν.real {x : ℝ | radiusMultiplier * normalization n < |x|}
    let U := radiusMultiplier * normalization n
    let J := ∫ t in Ioi (radiusMultiplier * normalization n),
      ν.real {x : ℝ | t < |x|}
    have hterm : ((n : ℝ) * T) * (J / T) = (n : ℝ) * J := by
      rw [div_eq_mul_inv]
      calc
        ((n : ℝ) * T) * (J * T⁻¹) = ((n : ℝ) * J) * (T * T⁻¹) := by ring
        _ = (n : ℝ) * J := by rw [hcancel, mul_one]
    change (n : ℝ) * T * (U + J / T) = (n : ℝ) * (U * T + J)
    calc
      (n : ℝ) * T * (U + J / T) = (n : ℝ) * T * U + (n : ℝ) * J := by
        rw [mul_add, hterm]
      _ = (n : ℝ) * (U * T + J) := by ring
  have hlimit' := hlimit.congr' heq
  have hconst : (((2 - α) / α) * radiusMultiplier ^ (-α)) * radiusMultiplier *
      (1 + 1 / (α - 1)) = discardedTailBiasConstant α radiusMultiplier := by
    have hpow : radiusMultiplier ^ (-α) * radiusMultiplier =
        radiusMultiplier ^ (1 - α) := by
      calc
        radiusMultiplier ^ (-α) * radiusMultiplier =
            radiusMultiplier ^ (-α) * radiusMultiplier ^ (1 : ℝ) := by
              rw [Real.rpow_one]
        _ = radiusMultiplier ^ ((-α) + 1) := by
              rw [← Real.rpow_add hradius]
        _ = radiusMultiplier ^ (1 - α) := by
              congr 1
              ring
    rw [show ((2 - α) / α) * radiusMultiplier ^ (-α) * radiusMultiplier *
        (1 + 1 / (α - 1)) = ((2 - α) / α) *
          (radiusMultiplier ^ (-α) * radiusMultiplier) *
            (1 + 1 / (α - 1)) by ring]
    rw [hpow]
    simp [discardedTailBiasConstant]
    field_simp [ne_of_gt (show 0 < α by linarith),
      ne_of_gt (show 0 < α - 1 by linarith)]
    ring
  rw [hconst] at hlimit'
  exact hlimit'

/-- For a centered law in the stable domain with `1 < α < 2`, the discarded
first moment gives an explicit eventual truncation-bias bound. This is the
centering input needed by the local block estimate. -/
theorem eventually_truncatedIncrementBias_le_of_stableNorming_of_index_gt_one
    {α radiusMultiplier thresholdMultiplier δ : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : 1 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hradius : 0 < radiusMultiplier)
    (hint : Integrable (fun x : ℝ => x) ν)
    (hcentered : (∫ x : ℝ, x ∂ν) = 0)
    (δpos : 0 < δ)
    (hsmall : δ * discardedTailBiasConstant α radiusMultiplier <
      thresholdMultiplier / 2)
    {length : ℕ → ℕ}
    (hlength : ∀ᶠ n in atTop, (length n : ℝ) / n ≤ δ) :
    ∀ᶠ n in atTop,
      (length n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
          normalization n ≤ thresholdMultiplier / 2 := by
  let biasRatio : ℕ → ℝ := fun n => (n : ℝ) *
    (∫ x, ({y : ℝ | radiusMultiplier * normalization n < |y|}).indicator
      (fun y => |y|) x ∂ν) / normalization n
  let biasConstant := discardedTailBiasConstant α radiusMultiplier
  have hbiasLimit := IsStableNorming.tendsto_nat_mul_discardedAbsFirstMoment_div_normalization_of_regularlyVaryingTail
    hnorm hα₀ hα₁ hα₂ htail hradius hint
  have hmargin : 0 < thresholdMultiplier / 2 - δ * biasConstant := by
    dsimp [biasConstant]
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
  have hnormPos : ∀ᶠ n : ℕ in atTop, 0 < normalization n :=
    hnorm.2.1.eventually (eventually_gt_atTop 0)
  filter_upwards [hlength, hratioEventually, hnormPos, eventually_gt_atTop (0 : ℕ)]
    with n hlengthn hratioN hscaleN hn
  have hmeanBound := abs_truncatedIncrementMean_le_integral_tail ν hint hcentered
    (radiusMultiplier * normalization n)
  have hmeanRatio : (n : ℝ) *
      |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
        normalization n ≤ biasRatio n := by
    dsimp [biasRatio]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmeanBound (by positivity)) hscaleN.le
  have hratioNonneg : 0 ≤ (length n : ℝ) / n :=
    div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hproduct : (length n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
          normalization n =
      ((length n : ℝ) / n) *
        ((n : ℝ) * |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
          normalization n) := by
    field_simp
  rw [hproduct]
  calc
    ((length n : ℝ) / n) *
        ((n : ℝ) * |truncatedIncrementMean ν
          (radiusMultiplier * normalization n)| / normalization n) ≤
        δ * biasRatio n := by
      exact mul_le_mul hlengthn hmeanRatio (by positivity) δpos.le
    _ ≤ δ * (biasConstant + η) :=
      mul_le_mul_of_nonneg_left (le_of_lt hratioN) δpos.le
    _ ≤ thresholdMultiplier / 2 := le_of_lt hbound

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

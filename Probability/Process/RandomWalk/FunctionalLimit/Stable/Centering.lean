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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

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

/-- The sine-centering condition used by Mogulskii at stable index one:
`n ∫ sin(x / B n) dν → 0`.  It is the source paper's `βₙ = o(1/n)`
condition, expressed at a specified norming sequence. -/
def IsMogulskiiIndexOneCentered (ν : Measure ℝ) (normalization : ℕ → ℝ) : Prop :=
  Tendsto (fun n : ℕ => (n : ℝ) *
    (∫ x, Real.sin (x / normalization n) ∂ν)) atTop (nhds 0)

/-- The cutoff-dependent constant controlling the hard-truncation bias at
stable index one under Mogulskii's sine-centering convention. -/
noncomputable def indexOneTruncationBiasConstant (radiusMultiplier : ℝ) : ℝ :=
  radiusMultiplier ^ 2 / 6 + radiusMultiplier⁻¹ + 1

/-- Compare a hard-truncated mean with the sine transform at its spatial
scale.  On the truncation interval, Mathlib's cubic bound
`Real.abs_sub_sin_le` is controlled by the truncated second moment; outside
that interval, `|sin| ≤ 1` is controlled by the tail probability. -/
theorem abs_truncatedIncrementMean_div_le_sineIntegral_add_truncatedMoment_tail
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius scale : ℝ} (hradius : 0 < radius) (hscale : 0 < scale) :
    |truncatedIncrementMean ν (radius * scale)| / scale ≤
      |∫ x, Real.sin (x / scale) ∂ν| +
        (radius / 6) * truncatedSecondMoment ν (radius * scale) / scale ^ 2 +
        ν.real {x : ℝ | radius * scale < |x|} := by
  let cutoff : ℝ := radius * scale
  let inside : Set ℝ := {x : ℝ | |x| ≤ cutoff}
  let outside : Set ℝ := {x : ℝ | cutoff < |x|}
  let scaledTrunc : ℝ → ℝ := fun x => truncatedIncrement cutoff x / scale
  let sine : ℝ → ℝ := fun x => Real.sin (x / scale)
  let errorBound : ℝ → ℝ := fun x =>
    inside.indicator (fun x => (radius / 6) * (x ^ 2 / scale ^ 2)) x +
      outside.indicator (fun _ => (1 : ℝ)) x
  have hinside : MeasurableSet inside := by
    dsimp [inside]
    exact measurableSet_le continuous_abs.measurable measurable_const
  have houtside : MeasurableSet outside := by
    dsimp [outside]
    exact measurableSet_lt measurable_const continuous_abs.measurable
  have hscaleTrunc : Integrable scaledTrunc ν := by
    dsimp [scaledTrunc, cutoff]
    exact (integrable_truncatedIncrement ν _).div_const scale
  have hsine : Integrable sine ν := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all ν fun x => ?_)
    dsimp [sine]
    exact Real.abs_sin_le_one _
  have hinsideBound : ∀ x ∈ inside,
      ‖(radius / 6) * (x ^ 2 / scale ^ 2)‖ ≤ radius ^ 3 / 6 := by
    intro x hx
    have hxabs : |x / scale| ≤ radius := by
      rw [abs_div, abs_of_pos hscale]
      exact (div_le_iff₀ hscale).2 (by simpa [inside, cutoff] using hx)
    have hsq : |x / scale| ^ 2 ≤ radius ^ 2 := by
      nlinarith [mul_self_le_mul_self (abs_nonneg (x / scale)) hxabs]
    have hsq' : (x / scale) ^ 2 ≤ radius ^ 2 := by
      simpa only [sq_abs] using hsq
    have hratioSq : x ^ 2 / scale ^ 2 ≤ radius ^ 2 := by
      simpa only [div_pow] using hsq'
    have hnonneg : 0 ≤ (radius / 6) * (x ^ 2 / scale ^ 2) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    have hcoeff : 0 ≤ radius / 6 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hratioSq hcoeff]
  have hinsideIntegrable : Integrable
      (inside.indicator (fun x => (radius / 6) * (x ^ 2 / scale ^ 2))) ν := by
    refine Integrable.of_bound (by fun_prop) (radius ^ 3 / 6) (ae_of_all ν fun x => ?_)
    by_cases hx : x ∈ inside
    · rw [Set.indicator_of_mem hx]
      exact hinsideBound x hx
    · rw [Set.indicator_of_notMem hx]
      rw [Real.norm_eq_abs, abs_zero]
      positivity
  have houtsideIntegrable : Integrable
      (outside.indicator (fun _ : ℝ => (1 : ℝ))) ν :=
    (integrable_const (1 : ℝ)).indicator houtside
  have herrorBoundIntegrable : Integrable errorBound ν := by
    dsimp [errorBound]
    exact hinsideIntegrable.add houtsideIntegrable
  have herr : Integrable (fun x => scaledTrunc x - sine x) ν :=
    hscaleTrunc.sub hsine
  have hpoint : ∀ x, |scaledTrunc x - sine x| ≤ errorBound x := by
    intro x
    by_cases hx : |x| ≤ cutoff
    · have hmem : x ∈ inside := hx
      have hnot : x ∉ outside := not_lt_of_ge hx
      have hx' : |x / scale| ≤ radius := by
        rw [abs_div, abs_of_pos hscale]
        exact (div_le_iff₀ hscale).2 (by simpa [cutoff] using hx)
      have htrunc : scaledTrunc x = x / scale := by
        dsimp [scaledTrunc, cutoff]
        rw [truncatedIncrement_of_abs_le (by simpa [cutoff] using hx)]
      change |scaledTrunc x - sine x| ≤
        inside.indicator (fun x => (radius / 6) * (x ^ 2 / scale ^ 2)) x +
          outside.indicator (fun _ => (1 : ℝ)) x
      rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnot, htrunc]
      simp only [sine, add_zero]
      have hsinErr := Real.abs_sub_sin_le (x / scale)
      have hcube : |x / scale| ^ 3 ≤ radius * (x / scale) ^ 2 := by
        calc
          |x / scale| ^ 3 = |x / scale| * (x / scale) ^ 2 := by
            rw [← sq_abs]
            ring
          _ ≤ radius * (x / scale) ^ 2 :=
            mul_le_mul_of_nonneg_right hx' (sq_nonneg _)
      calc
        |x / scale - Real.sin (x / scale)| ≤ |x / scale| ^ 3 / 6 := hsinErr
        _ ≤ (radius / 6) * (x / scale) ^ 2 := by nlinarith [hcube]
        _ = (radius / 6) * (x ^ 2 / scale ^ 2) := by rw [div_pow]
    · have htail : cutoff < |x| := lt_of_not_ge hx
      have hnot : x ∉ inside := by simpa [inside] using hx
      have hmem : x ∈ outside := htail
      have htrunc : scaledTrunc x = 0 := by
        dsimp [scaledTrunc, cutoff]
        rw [truncatedIncrement_of_lt_abs htail, zero_div]
      change |scaledTrunc x - sine x| ≤
        inside.indicator (fun x => (radius / 6) * (x ^ 2 / scale ^ 2)) x +
          outside.indicator (fun _ => (1 : ℝ)) x
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_mem hmem, htrunc]
      simp only [sine, zero_sub]
      simpa only [abs_neg, zero_add] using Real.abs_sin_le_one (x / scale)
  have herror : ∫ x, |scaledTrunc x - sine x| ∂ν ≤ ∫ x, errorBound x ∂ν :=
    integral_mono herr.norm herrorBoundIntegrable hpoint
  have hinsideIntegral :
      (∫ x, inside.indicator
        (fun x => (radius / 6) * (x ^ 2 / scale ^ 2)) x ∂ν) =
        (radius / 6) * truncatedSecondMoment ν cutoff / scale ^ 2 := by
    rw [integral_indicator hinside]
    have hset : inside = Set.Icc (-cutoff) cutoff := by
      ext x
      simp only [inside, Set.mem_ofPred_eq, Set.mem_Icc]
      exact abs_le
    rw [hset, truncatedSecondMoment]
    rw [show (fun x : ℝ => (radius / 6) * (x ^ 2 / scale ^ 2) : ℝ → ℝ) =
        fun x => ((radius / 6) / scale ^ 2) * x ^ 2 by
      funext x
      ring]
    rw [integral_const_mul]
    ring
  have houtsideIntegral :
      (∫ x, outside.indicator (fun _ : ℝ => (1 : ℝ)) x ∂ν) = ν.real outside := by
    rw [integral_indicator houtside, setIntegral_const, smul_eq_mul]
    simp [Measure.real, outside, cutoff]
  have herrorEq : ∫ x, errorBound x ∂ν =
      (radius / 6) * truncatedSecondMoment ν cutoff / scale ^ 2 +
        ν.real outside := by
    dsimp [errorBound]
    rw [integral_add hinsideIntegrable houtsideIntegrable,
      hinsideIntegral, houtsideIntegral]
  have hmeanEq :
      (∫ x, scaledTrunc x ∂ν) =
        (∫ x, truncatedIncrement cutoff x ∂ν) / scale := by
    rw [show scaledTrunc = fun x => scale⁻¹ * truncatedIncrement cutoff x by
      funext x
      dsimp [scaledTrunc]
      ring]
    rw [integral_const_mul]
    ring
  have hsum :
      (∫ x, scaledTrunc x ∂ν) =
        (∫ x, sine x ∂ν) + ∫ x, (scaledTrunc x - sine x) ∂ν := by
    calc
      (∫ x, scaledTrunc x ∂ν) =
          ∫ x, (sine x + (scaledTrunc x - sine x)) ∂ν := by
            congr 1
            funext x
            ring
      _ = _ := integral_add hsine herr
  have hnormMean :
      ‖∫ x, scaledTrunc x ∂ν‖ ≤
        ‖∫ x, sine x ∂ν‖ + ∫ x, ‖scaledTrunc x - sine x‖ ∂ν := by
    calc
      ‖∫ x, scaledTrunc x ∂ν‖ =
          ‖(∫ x, sine x ∂ν) + ∫ x, (scaledTrunc x - sine x) ∂ν‖ := by rw [hsum]
      _ ≤ ‖∫ x, sine x ∂ν‖ + ‖∫ x, (scaledTrunc x - sine x) ∂ν‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl
        (norm_integral_le_integral_norm (fun x => scaledTrunc x - sine x))
  have herrorNorm : ∫ x, ‖scaledTrunc x - sine x‖ ∂ν ≤ ∫ x, errorBound x ∂ν := by
    simpa only [Real.norm_eq_abs] using herror
  have hfinal := hnormMean.trans
    (add_le_add le_rfl herrorNorm)
  simpa [hmeanEq, herrorEq, sine, outside, cutoff, truncatedIncrementMean,
    Real.norm_eq_abs, abs_div, abs_of_pos hscale, add_assoc] using hfinal

/-- Mogulskii's index-one sine-centering condition bounds the normalized
hard-truncation bias.  The proof compares the truncated mean with the source
sine transform; the error is controlled by the already established tail and
truncated-second-moment limits. -/
theorem IsStableNorming.eventually_nat_mul_abs_truncatedIncrementMean_div_le_of_index_one
    {radiusMultiplier : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ}
    (hnorm : IsStableNorming 1 ν normalization)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-1))
    (hradius : 0 < radiusMultiplier)
    (hcenter : IsMogulskiiIndexOneCentered ν normalization) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * |truncatedIncrementMean ν
        (radiusMultiplier * normalization n)| / normalization n ≤
          indexOneTruncationBiasConstant radiusMultiplier := by
  let sineTerm : ℕ → ℝ := fun n => (n : ℝ) *
    |∫ x, Real.sin (x / normalization n) ∂ν|
  let momentTerm : ℕ → ℝ := fun n => (radiusMultiplier / 6) *
    ((n : ℝ) * truncatedSecondMoment ν (radiusMultiplier * normalization n) /
      normalization n ^ 2)
  let tailTerm : ℕ → ℝ := fun n => (n : ℝ) *
    ν.real {x : ℝ | radiusMultiplier * normalization n < |x|}
  let errorTerm : ℕ → ℝ := fun n => sineTerm n + momentTerm n + tailTerm n
  have hcenterAbs : Tendsto sineTerm atTop (nhds 0) := by
    have habs := (continuous_abs.tendsto 0).comp hcenter
    have heq : (fun n : ℕ => |(n : ℝ) *
        (∫ x, Real.sin (x / normalization n) ∂ν)|) = sineTerm := by
      funext n
      dsimp [sineTerm]
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    have habs' : Tendsto
        (fun n : ℕ => |(n : ℝ) *
          (∫ x, Real.sin (x / normalization n) ∂ν)|) atTop (nhds 0) := by
      change Tendsto (abs ∘ (fun n : ℕ => (n : ℝ) *
        (∫ x, Real.sin (x / normalization n) ∂ν))) atTop (nhds 0)
      simpa only [abs_zero] using habs
    rw [← heq]
    exact habs'
  have htailLimit := hnorm.tendsto_nat_mul_twoSidedTail_mul_of_regularlyVarying
    (show 0 < (1 : ℝ) by norm_num) (show (1 : ℝ) < 2 by norm_num) htail hradius
  have htailConstant : ((2 - (1 : ℝ)) / 1) * radiusMultiplier ^ (-(1 : ℝ)) =
      radiusMultiplier⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hradius), Real.rpow_one]
    norm_num
  have htailLimit' : Tendsto tailTerm atTop (nhds radiusMultiplier⁻¹) := by
    simpa only [tailTerm, htailConstant] using htailLimit
  have hmomentLimit := hnorm.tendsto_nat_mul_truncatedSecondMoment_mul_div_sq
    (show 0 < (1 : ℝ) by norm_num) (show (1 : ℝ) < 2 by norm_num) htail hradius
  have hmomentLimit' : Tendsto momentTerm atTop (nhds ((radiusMultiplier / 6) * radiusMultiplier)) := by
    convert tendsto_const_nhds.mul hmomentLimit using 1
    norm_num [momentTerm, Real.rpow_one]
  have herrorLimit : Tendsto errorTerm atTop
      (nhds (0 + ((radiusMultiplier / 6) * radiusMultiplier + radiusMultiplier⁻¹))) := by
    simpa [errorTerm, add_assoc] using hcenterAbs.add (hmomentLimit'.add htailLimit')
  have hmargin :
      0 + ((radiusMultiplier / 6) * radiusMultiplier + radiusMultiplier⁻¹) <
        indexOneTruncationBiasConstant radiusMultiplier := by
    have hmul : (radiusMultiplier / 6) * radiusMultiplier =
        radiusMultiplier ^ 2 / 6 := by ring
    rw [hmul]
    dsimp [indexOneTruncationBiasConstant]
    linarith
  have herrorEventually : ∀ᶠ n in atTop,
      errorTerm n < indexOneTruncationBiasConstant radiusMultiplier := by
    exact herrorLimit.eventually (Iio_mem_nhds hmargin)
  have hnormPos : ∀ᶠ n : ℕ in atTop, 0 < normalization n :=
    hnorm.2.1.eventually (eventually_gt_atTop 0)
  filter_upwards [herrorEventually, hnormPos] with n herr hscale
  have hcomparison := abs_truncatedIncrementMean_div_le_sineIntegral_add_truncatedMoment_tail
    ν hradius hscale
  have hbound :
      (n : ℝ) * |truncatedIncrementMean ν
          (radiusMultiplier * normalization n)| / normalization n ≤ errorTerm n := by
    have hmul := mul_le_mul_of_nonneg_left hcomparison (Nat.cast_nonneg n)
    calc
      (n : ℝ) * |truncatedIncrementMean ν
          (radiusMultiplier * normalization n)| / normalization n =
          (n : ℝ) * (|truncatedIncrementMean ν
            (radiusMultiplier * normalization n)| / normalization n) := by ring
      _ ≤ (n : ℝ) *
          (|∫ x, Real.sin (x / normalization n) ∂ν| +
            (radiusMultiplier / 6) * truncatedSecondMoment ν
              (radiusMultiplier * normalization n) / normalization n ^ 2 +
            ν.real {x : ℝ | radiusMultiplier * normalization n < |x|}) := hmul
      _ = errorTerm n := by
        dsimp [errorTerm, sineTerm, momentTerm, tailTerm]
        ring
  exact hbound.trans (le_of_lt herr)

/-- The index-one sine-centering condition supplies the bias margin for any
block whose length is at most a sufficiently small fraction of the horizon. -/
theorem eventually_truncatedIncrementBias_le_of_stableNorming_of_index_one
    {radiusMultiplier thresholdMultiplier δ : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ}
    (hnorm : IsStableNorming 1 ν normalization)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-1))
    (hradius : 0 < radiusMultiplier)
    (hcenter : IsMogulskiiIndexOneCentered ν normalization)
    (δpos : 0 < δ)
    (hsmall : δ * indexOneTruncationBiasConstant radiusMultiplier <
      thresholdMultiplier / 2)
    {length : ℕ → ℕ}
    (hlength : ∀ᶠ n in atTop, (length n : ℝ) / n ≤ δ) :
    ∀ᶠ n in atTop,
      (length n : ℝ) * |truncatedIncrementMean ν
        (radiusMultiplier * normalization n)| / normalization n ≤
          thresholdMultiplier / 2 := by
  have hbias := IsStableNorming.eventually_nat_mul_abs_truncatedIncrementMean_div_le_of_index_one
    hnorm htail hradius hcenter
  have hnormPos : ∀ᶠ n : ℕ in atTop, 0 < normalization n :=
    hnorm.2.1.eventually (eventually_gt_atTop 0)
  filter_upwards [hlength, hbias, hnormPos, eventually_gt_atTop (0 : ℕ)]
    with n hlengthn hbiasn hscale hn
  have hratioNonneg : 0 ≤ (length n : ℝ) / n :=
    div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hbiasNonneg : 0 ≤
      (n : ℝ) * |truncatedIncrementMean ν
        (radiusMultiplier * normalization n)| / normalization n := by
    positivity
  have hproduct :
      (length n : ℝ) * |truncatedIncrementMean ν
          (radiusMultiplier * normalization n)| / normalization n =
        ((length n : ℝ) / n) *
          ((n : ℝ) * |truncatedIncrementMean ν
            (radiusMultiplier * normalization n)| / normalization n) := by
    field_simp
  rw [hproduct]
  refine le_of_lt ?_
  calc
    ((length n : ℝ) / n) *
        ((n : ℝ) * |truncatedIncrementMean ν
          (radiusMultiplier * normalization n)| / normalization n) ≤
        δ * ((n : ℝ) * |truncatedIncrementMean ν
          (radiusMultiplier * normalization n)| / normalization n) :=
      mul_le_mul_of_nonneg_right hlengthn hbiasNonneg
    _ ≤ δ * indexOneTruncationBiasConstant radiusMultiplier :=
      mul_le_mul_of_nonneg_left hbiasn δpos.le
    _ < thresholdMultiplier / 2 := hsmall

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

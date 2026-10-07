/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Moments.Variance
public import Probability.Distributions.DomainOfAttraction.Basic
public import Probability.Distributions.Moments.Truncated
public import Probability.Distributions.Stable.Attraction
public import Probability.Distributions.Stable.Attraction.Norming
public import Probability.Distributions.Stable.Gaussian
public import Probability.Distributions.Stable.Attraction.NormingRatios.Index
public import Probability.Distributions.Stable.Attraction.NormingRatios.RegularVariation
public import Probability.Sequence.IID

/-!
# The finite-variance normal domain of attraction

A centered probability law with positive finite second moment belongs to the
domain of attraction of the standard Gaussian under the canonical normalization
`sqrt (n * variance)`. The normalization also satisfies the quadratic stable
norming relation defined from the law's truncated second moment.

This is the finite-variance part of the exponent-two normal domain of
attraction. No assertion about infinite-variance normal attraction is made.
-/

open Filter MeasureTheory
open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory

/-- For a probability law with positive finite second moment, the quadratic
stable norming relation holds for the canonical second-moment scale
`sqrt (n * secondMoment)`. -/
theorem isStableNorming_two_of_integrable_sq
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hsecondMoment : 0 < ∫ x, x ^ 2 ∂ν) :
    IsStableNorming 2 ν
      (fun n => Real.sqrt ((n : ℝ) * ∫ x, x ^ 2 ∂ν)) := by
  let secondMoment : ℝ := ∫ x, x ^ 2 ∂ν
  let normalization : ℕ → ℝ := fun n => Real.sqrt ((n : ℝ) * secondMoment)
  have hsecondMoment' : 0 < secondMoment := by simpa [secondMoment] using hsecondMoment
  have hnormalizationPos : ∀ n, 0 < n → 0 < normalization n := by
    intro n hn
    dsimp [normalization]
    exact Real.sqrt_pos.2 (mul_pos (by exact_mod_cast hn) hsecondMoment')
  have hnormalizationTop : Tendsto normalization atTop atTop := by
    have hnTop : Tendsto (fun n : ℕ => (n : ℝ) * secondMoment) atTop atTop := by
      simpa [mul_comm] using
        (tendsto_natCast_atTop_atTop.const_mul_atTop hsecondMoment')
    change Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) * secondMoment)) atTop atTop
    exact Real.tendsto_sqrt_atTop.comp hnTop
  have htruncated : Tendsto (fun u : ℝ => truncatedSecondMoment ν u) atTop
      (nhds secondMoment) := by
    simpa [secondMoment] using tendsto_truncatedSecondMoment ν hsquare
  have htruncatedNorm : Tendsto
      (fun n : ℕ => truncatedSecondMoment ν (normalization n)) atTop
      (nhds secondMoment) := htruncated.comp hnormalizationTop
  have htruncatedPos : ∀ᶠ n : ℕ in atTop,
      0 < truncatedSecondMoment ν (normalization n) :=
    htruncatedNorm.eventually (Ioi_mem_nhds hsecondMoment')
  have hnormRatio : Tendsto
      (fun n : ℕ => normalization n ^ (2 : ℝ) /
        stableSlowVariation 2 ν (normalization n) / (n : ℝ))
      atTop (nhds 1) := by
    have hlimit : Tendsto
        (fun n : ℕ => secondMoment / truncatedSecondMoment ν (normalization n))
        atTop (nhds 1) := by
      have hinv := htruncatedNorm.inv₀ hsecondMoment'.ne'
      have hmul : Tendsto
          (fun n : ℕ => secondMoment *
            (truncatedSecondMoment ν (normalization n))⁻¹)
          atTop (nhds (secondMoment * secondMoment⁻¹)) :=
        tendsto_const_nhds.mul hinv
      convert hmul using 1 <;> simp [div_eq_mul_inv, hsecondMoment'.ne']
    apply hlimit.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ), htruncatedPos]
      with n hn hmoment
    have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hscaleSq : normalization n ^ (2 : ℝ) = (n : ℝ) * secondMoment := by
      calc
        normalization n ^ (2 : ℝ) = normalization n ^ (2 : ℕ) :=
          Real.rpow_natCast (normalization n) 2
        _ = (Real.sqrt ((n : ℝ) * secondMoment)) ^ 2 := rfl
        _ = (n : ℝ) * secondMoment :=
          Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) hsecondMoment'.le)
    rw [stableSlowVariation_two, hscaleSq]
    dsimp [secondMoment]
    field_simp [hnReal, hmoment.ne']
  have hnorming : IsStableNorming 2 ν normalization :=
    ⟨hnormalizationPos, hnormalizationTop, hnormRatio⟩
  simpa [normalization, secondMoment] using hnorming

/-- A finite positive second moment makes the exponent-two factor `L*` slowly
varying: its truncated second moments converge to the full second moment. -/
theorem stableSlowVariation_two_isSlowlyVarying_of_integrable_sq
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hsecondMoment : 0 < ∫ x, x ^ 2 ∂ν) :
    Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation 2 ν) := by
  have hmoment := tendsto_truncatedSecondMoment ν hsquare
  have hslow : Asymptotics.IsSlowlyVaryingAtTop (truncatedSecondMoment ν) :=
    Asymptotics.IsSlowlyVaryingAtTop.of_tendsto_pos hsecondMoment hmoment
  rw [show stableSlowVariation 2 ν = truncatedSecondMoment ν by
    funext u
    exact stableSlowVariation_two ν u]
  exact hslow

/-- Every attraction to the standard Gaussian has the corresponding
characteristic-function consequences: the squared-modulus defect is regularly
varying at zero with index `2`, and along the specified normalization its
one-step defect is asymptotic to `1 / n`.

This statement uses only distributional attraction. It does not identify the
defect with the truncated second moment, so the finite-variance and
infinite-variance norming arguments remain distinct. -/
theorem IsInDomainOfAttractionAlong.gaussian_defect_data
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    Asymptotics.IsRegularlyVaryingAtZero
        (fun u : ℝ => 1 - ‖charFun ν u‖ ^ 2) 2 ∧
      Tendsto scale atTop atTop ∧
      Tendsto (fun n : ℕ => (n : ℝ) *
        (1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2)) atTop (nhds 1) := by
  let hlimit : IsAlphaStable 2 (gaussianReal 0 1) :=
    (isStrictlyAlphaStable_gaussianReal_zero (by norm_num)).isAlphaStable
  have hreg : Asymptotics.IsRegularlyVaryingAtZero
      (fun u : ℝ => 1 - ‖charFun ν u‖ ^ 2) 2 := by
    exact h.isRegularlyVarying_normDefect_atZero hlimit
  obtain ⟨c, hc, hchar⟩ := hlimit.exists_pos_norm_charFun_eq_exp
  have hcharAtOne :
      ‖charFun (gaussianReal 0 1) 1‖ = Real.exp (-(1 / 2 : ℝ)) := by
    rw [charFun_gaussianReal, Complex.norm_exp]
    norm_num
  have hcEq : c = 1 / 2 := by
    have h' := hchar 1
    rw [hcharAtOne] at h'
    have hexp : Real.exp (-c) = Real.exp (-(1 / 2 : ℝ)) := by
      simpa using h'.symm
    have harg := Real.exp_injective hexp
    linarith
  have hdefect :=
    (h.tendsto_log_norm_charFun_and_norm_defect_of_charFun_norm
      hlimit c hc hchar 1).2
  have hdefect' : Tendsto (fun n : ℕ => (n : ℝ) *
      (1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2)) atTop (nhds 1) := by
    simpa [hcEq] using hdefect
  exact ⟨hreg, h.tendsto_scale_atTop hlimit, hdefect'⟩

/-- A centered probability law with positive finite second moment is in the
standard Gaussian domain of attraction along the canonical normalization
`sqrt (n * variance)`, with zero centering. -/
theorem isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_integrable_sq
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hsecondMoment : 0 < ∫ x, x ^ 2 ∂ν) :
    IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      (fun n => Real.sqrt ((n : ℝ) * ∫ x, x ^ 2 ∂ν)) (fun _ => 0) := by
  let secondMoment : ℝ := ∫ x, x ^ 2 ∂ν
  let sigma : ℝ := Real.sqrt secondMoment
  let normalization : ℕ → ℝ := fun n => Real.sqrt ((n : ℝ) * secondMoment)
  let P := iidSequenceLaw ν
  let X : ℕ → (ℕ → ℝ) → ℝ := fun i sequence => sequence i
  have hXlaw (i : ℕ) : HasLaw (X i) ν P := by
    refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
    change P.map (fun sequence => sequence i) = ν
    exact iidSequenceLaw_map_apply ν i
  have hXid (i : ℕ) : IdentDistrib (X i) id P ν :=
    (hXlaw i).identDistrib HasLaw.id
  have hIdMemLp : MemLp id 2 ν := by
    apply (memLp_two_iff_integrable_sq
      stronglyMeasurable_id.aestronglyMeasurable).2
    simpa [id] using hsquare
  have hXmem : MemLp (X 0) 2 P := (hXid 0).memLp_iff.2 hIdMemLp
  have hXmean : P[X 0] = 0 := by
    rw [(hXid 0).integral_eq]
    exact hcentered
  have hXvariance : ProbabilityTheory.variance (X 0) P = secondMoment := by
    calc
      ProbabilityTheory.variance (X 0) P = ProbabilityTheory.variance id ν :=
        (hXlaw 0).variance_eq
      _ = ∫ x, x ^ 2 ∂ν := by
        rw [variance_eq_sub hIdMemLp]
        simp [id, hcentered]
      _ = secondMoment := rfl
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    exact Real.sqrt_pos.2 (by simpa [secondMoment] using hsecondMoment)
  have hCLT : TendstoInDistribution
      (fun (n : ℕ) sequence => (Real.sqrt (n : ℝ))⁻¹ *
        (∑ k ∈ Finset.range n, X k sequence - (n : ℝ) * P[X 0]))
      atTop id (fun _ => P) (gaussianReal 0 secondMoment.toNNReal) := by
    have hCLT' := tendstoInDistribution_inv_sqrt_mul_sum_sub
      (P := P) (P' := gaussianReal 0
        (ProbabilityTheory.variance (X 0) P).toNNReal)
      (X := X) (Y := id) HasLaw.id hXmem
      (iidSequenceLaw_independent ν) (fun i => (hXid i).trans (hXid 0).symm)
    simpa [hXvariance] using hCLT'
  have hbase : IsInDomainOfAttractionAlong ν
      (gaussianReal 0 secondMoment.toNNReal)
      (fun n => Real.sqrt (n : ℝ)) (fun _ => 0) := by
    refine ⟨?_, ?_⟩
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact Real.sqrt_pos.2 (by exact_mod_cast hn)
    · change TendstoInDistribution
        (fun (n : ℕ) sequence => (Real.sqrt (n : ℝ))⁻¹ *
          ((∑ k ∈ Finset.range n, sequence k) - (0 : ℝ)))
        atTop id (fun _ => P) (gaussianReal 0 secondMoment.toNNReal)
      simpa [P, X, hXmean] using hCLT
  have hrescaled := hbase.rescale sigma⁻¹ (inv_pos.mpr hsigma)
  have hmap : (gaussianReal 0 secondMoment.toNNReal).map
      (fun x => sigma⁻¹ * x) = gaussianReal 0 1 := by
    have hmap' := gaussianReal_map_div_const
      (μ := (0 : ℝ)) (v := secondMoment.toNNReal) sigma
    have hvarianceNN : secondMoment.toNNReal /
        ⟨sigma ^ 2, sq_nonneg sigma⟩ = 1 := by
      apply NNReal.eq
      change (Real.toNNReal secondMoment : ℝ) / sigma ^ 2 = 1
      rw [Real.coe_toNNReal', max_eq_left (by positivity : 0 ≤ secondMoment)]
      rw [Real.sq_sqrt (by positivity : 0 ≤ secondMoment)]
      exact div_self (ne_of_gt (by simpa [secondMoment] using hsecondMoment))
    have hmap'' : (gaussianReal 0 secondMoment.toNNReal).map
        (fun x => x / sigma) = gaussianReal 0 1 := by
      rw [hmap']
      rw [zero_div]
      exact congrArg (gaussianReal 0) hvarianceNN
    have hfun : (fun x : ℝ => sigma⁻¹ * x) = fun x => x / sigma := by
      funext x
      simp [div_eq_mul_inv, mul_comm]
    rw [hfun]
    exact hmap''
  have hcanonical : (fun n : ℕ => sigma * Real.sqrt (n : ℝ)) =
      fun n : ℕ => Real.sqrt ((n : ℝ) * secondMoment) := by
    funext n
    dsimp [sigma]
    have hsecondMomentPos : 0 < secondMoment := by
      simpa [secondMoment] using hsecondMoment
    calc
      Real.sqrt secondMoment * Real.sqrt (n : ℝ) =
          Real.sqrt (secondMoment * (n : ℝ)) :=
        (Real.sqrt_mul hsecondMomentPos.le (n : ℝ)).symm
      _ = Real.sqrt ((n : ℝ) * secondMoment) := by rw [mul_comm]
  have hstandard : TendstoInDistribution
      (normalizedIidSum (fun n : ℕ => Real.sqrt ((n : ℝ) * secondMoment))
        (fun _ => 0))
      atTop id (fun _ => P) (gaussianReal 0 1) := by
    have hlimitLaw :
        ((gaussianReal 0 secondMoment.toNNReal).map
          (fun x => sigma⁻¹ * x)).map id =
          (gaussianReal 0 1).map id :=
      congrArg (fun μ : Measure ℝ => μ.map id) hmap
    have hcongrLimit := hrescaled.2.congr_limit aemeasurable_id hlimitLaw
    simpa only [inv_inv, hcanonical] using hcongrLimit
  have hcanonicalTID : TendstoInDistribution
      (normalizedIidSum (fun n : ℕ => Real.sqrt ((n : ℝ) * secondMoment))
        (fun _ => 0))
      atTop id (fun _ => P) (gaussianReal 0 1) := by
    exact hstandard
  refine ⟨?_, hcanonicalTID⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply Real.sqrt_pos.2
  exact mul_pos (by exact_mod_cast hn : 0 < (n : ℝ)) hsecondMoment

/-- For a standard Gaussian attraction scale, the endpoint defect-to-moment
asymptotic is exactly the missing input needed to recover quadratic stable
norming. The hypothesis
`V(x) / (x^2 * (1 - ‖φ(1/x)‖^2)) → 1` is the exponent-two inverse-Tauberian
step; this theorem does not derive it from Gaussian attraction. -/
theorem IsInDomainOfAttractionAlong.isStableNorming_two_of_tendsto_truncatedSecondMoment_div_scaledCosineDefect
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center)
    (hscalePos : ∀ n, 0 < n → 0 < scale n)
    (hcompat : Tendsto
      (fun x : ℝ => truncatedSecondMoment ν x /
        (x ^ 2 * (1 - ‖charFun ν (x⁻¹)‖ ^ 2)))
      atTop (nhds 1)) :
    IsStableNorming 2 ν scale := by
  let hlimit : IsAlphaStable 2 (gaussianReal 0 1) :=
    (isStrictlyAlphaStable_gaussianReal_zero (by norm_num)).isAlphaStable
  have hscaleTop : Tendsto scale atTop atTop := h.tendsto_scale_atTop hlimit
  have hdefect : Tendsto
      (fun n : ℕ => (n : ℝ) *
        (1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2))
      atTop (nhds 1) := h.gaussian_defect_data.2.2
  have hcompatSeq : Tendsto
      (fun n : ℕ => truncatedSecondMoment ν (scale n) /
        (scale n ^ 2 * (1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2)))
      atTop (nhds 1) := hcompat.comp hscaleTop
  have hproduct := hcompatSeq.mul hdefect
  have hnatPos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact_mod_cast hn
  have hdefectEq : (fun n : ℕ =>
      truncatedSecondMoment ν (scale n) /
        (scale n ^ 2 * (1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2)) *
        ((n : ℝ) * (1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2))) =ᶠ[atTop]
      fun n => (n : ℝ) * truncatedSecondMoment ν (scale n) / scale n ^ 2 := by
    filter_upwards [h.eventually_scale_pos, hnatPos,
      hdefect.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hsn hnn hdn
    have hsn' : scale n ≠ 0 := ne_of_gt hsn
    have hnn' : (n : ℝ) ≠ 0 := ne_of_gt hnn
    have hd : 1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2 ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hdn
      norm_num at hdn
    field_simp [hsn', hnn', hd]
  have hratio : Tendsto
      (fun n : ℕ => (n : ℝ) * truncatedSecondMoment ν (scale n) /
        scale n ^ 2) atTop (nhds 1) := by
    simpa using hproduct.congr' hdefectEq
  have hratioPos : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * truncatedSecondMoment ν (scale n) / scale n ^ 2 > 0 :=
    hratio.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hmomentPos : ∀ᶠ n : ℕ in atTop,
      0 < truncatedSecondMoment ν (scale n) := by
    filter_upwards [hratioPos, hnatPos, h.eventually_scale_pos]
      with n hq hn hsn
    have hnum : 0 < (n : ℝ) * truncatedSecondMoment ν (scale n) :=
      (div_pos_iff_of_pos_right (sq_pos_of_pos hsn)).mp hq
    exact (mul_pos_iff_of_pos_left hn).mp hnum
  have hinv := hratio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hinvEq : (fun n : ℕ =>
      ((n : ℝ) * truncatedSecondMoment ν (scale n) / scale n ^ 2)⁻¹) =ᶠ[atTop]
      fun n => scale n ^ (2 : ℝ) /
        truncatedSecondMoment ν (scale n) / (n : ℝ) := by
    filter_upwards [hmomentPos, hnatPos, h.eventually_scale_pos] with n hmoment hn hsn
    have hpow : scale n ^ (2 : ℝ) = scale n ^ (2 : ℕ) :=
      Real.rpow_natCast (scale n) 2
    rw [hpow]
    have hnn' : (n : ℝ) ≠ 0 := ne_of_gt hn
    field_simp [hmoment.ne', hnn']
  have hnormRatio : Tendsto
      (fun n : ℕ => scale n ^ (2 : ℝ) /
        truncatedSecondMoment ν (scale n) / (n : ℝ))
      atTop (nhds 1) := by
    simpa using hinv.congr' hinvEq
  refine ⟨hscalePos, hscaleTop, ?_⟩
  simpa only [stableSlowVariation_two] using hnormRatio

/-- A centered probability law with positive finite second moment belongs to
the strictly `2`-stable domain of attraction of the standard Gaussian, with
the canonical second-moment normalization retained as a witness. -/
theorem isInAlphaStableDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_integrable_sq
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hsecondMoment : 0 < ∫ x, x ^ 2 ∂ν) :
    IsInAlphaStableDomainOfAttractionAlong 2 ν (gaussianReal 0 1)
      (fun n => Real.sqrt ((n : ℝ) * ∫ x, x ^ 2 ∂ν)) (fun _ => 0) := by
  refine ⟨(isStrictlyAlphaStable_gaussianReal_zero (by norm_num)).isAlphaStable, ?_⟩
  exact isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_integrable_sq
    ν hcentered hsquare hsecondMoment

end ProbabilityTheory

end

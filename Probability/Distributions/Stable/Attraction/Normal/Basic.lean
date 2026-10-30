/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Moments.Variance
public import Probability.Distributions.DomainOfAttraction.Basic
import Probability.Distributions.DomainOfAttraction.Normalization
public import Probability.Distributions.Moments.Real
public import Probability.Distributions.Moments.Truncated.Basic
public import Probability.Distributions.Stable.Domain.Attraction
public import Probability.Distributions.Stable.Gaussian.Basic
public import Probability.Distributions.Stable.Attraction.NormingRatios.Index
public import Probability.Distributions.Stable.Attraction.NormingRatios.RegularVariation
public import Probability.Sequence.IID.Basic

/-!
# The finite-variance normal domain of attraction

## Public declarations

- `IsInDomainOfAttractionAlong.gaussian_defect_data`: attraction to the
  standard Gaussian implies regular variation of
  $1-|\widehat\nu(u)|^2$ with index $2$, and
  $n(1-|\widehat\nu(a_n^{-1})|^2)\to1$.
- `IsInDomainOfAttractionAlong.tendsto_scaledGaussianNormDefect`: for every
  $t>0$, $n(1-|\widehat\nu(t/a_n)|^2)\to t^2$.
- `IsInDomainOfAttractionAlong.tendsto_gaussian_quadraticDefectCancellation`:
  $n(4D(t/a_n)-D(2t/a_n))\to0$, where
  $D(u)=1-|\widehat\nu(u)|^2$.
- `isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_posSecondMoment`:
  a centered law with positive second moment converges to the standard
  Gaussian under $a_n=\sqrt{n\int x^2\,d\nu}$.
- `isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_unitSecondMoment`:
  under centered unit second moment, the same conclusion holds with
  $a_n=\sqrt n$.
- `isInAlphaStableDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_posSecondMoment`:
  the preceding positive-second-moment convergence also supplies the strictly
  $2$-stable domain-of-attraction witness.

This is the finite-variance part of the exponent-two normal domain of
attraction. No assertion about infinite-variance normal attraction is made.
-/

open Filter MeasureTheory
open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory

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

/-- Under Gaussian attraction, the scaled squared-modulus defect converges at
each fixed positive frequency to the Gaussian quadratic defect. This is the
fixed-frequency specialization of the source characteristic-function limit. -/
theorem IsInDomainOfAttractionAlong.tendsto_scaledGaussianNormDefect
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center)
    {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun n : ℕ => (n : ℝ) *
        (1 - ‖charFun ν (t * (scale n)⁻¹)‖ ^ 2))
      atTop (nhds (t ^ (2 : ℝ))) := by
  let hlimit : IsAlphaStable 2 (gaussianReal 0 1) :=
    (isStrictlyAlphaStable_gaussianReal_zero (by norm_num)).isAlphaStable
  let defect : ℝ → ℝ := fun u => 1 - ‖charFun ν u‖ ^ 2
  have hdata := h.gaussian_defect_data
  have hratio := h.tendsto_normDefect_ratio_nhdsGT_zero hlimit t ht
  have hinv : Tendsto (fun n : ℕ => (scale n)⁻¹) atTop
      (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_inv_atTop_nhdsGT_zero.comp hdata.2.1
  have hratioSeq : Tendsto
      ((fun u : ℝ => defect (t * u) / defect u) ∘
        fun n : ℕ => (scale n)⁻¹)
      atTop (nhds (t ^ (2 : ℝ))) := by
    simpa only [defect] using hratio.comp hinv
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) * defect ((scale n)⁻¹))
      atTop (nhds 1) := by
    simpa [defect] using hdata.2.2
  have hdenPos : ∀ᶠ n : ℕ in atTop, 0 < defect ((scale n)⁻¹) :=
    hinv.eventually hdata.1.eventually_pos
  have hproduct := hratioSeq.mul hbase
  have heq : (fun n : ℕ =>
      defect (t * (scale n)⁻¹) / defect ((scale n)⁻¹) *
        ((n : ℝ) * defect ((scale n)⁻¹))) =ᶠ[atTop]
      fun n => (n : ℝ) * defect (t * (scale n)⁻¹) := by
    filter_upwards [hdenPos] with n hn
    dsimp [defect]
    calc
      _ = ((1 - ‖charFun ν (t * (scale n)⁻¹)‖ ^ 2) /
            (1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2) *
            (1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2)) * (n : ℝ) := by ring
      _ = (1 - ‖charFun ν (t * (scale n)⁻¹)‖ ^ 2) * (n : ℝ) := by
        rw [div_mul_cancel₀ _ (ne_of_gt hn)]
      _ = (n : ℝ) * (1 - ‖charFun ν (t * (scale n)⁻¹)‖ ^ 2) := by ring
  have hfinal := hproduct.congr' heq
  simpa [defect] using hfinal

/-- Gaussian attraction annihilates the second-order difference
`4 D(t/aₙ) - D(2t/aₙ)` at scale `n`. This is a source-derived endpoint
identity that isolates the quadratic part of the defect before any
truncated-moment converse is applied. -/
theorem IsInDomainOfAttractionAlong.tendsto_gaussian_quadraticDefectCancellation
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center)
    {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun n : ℕ => (n : ℝ) *
        (4 * (1 - ‖charFun ν (t * (scale n)⁻¹)‖ ^ 2) -
          (1 - ‖charFun ν ((2 * t) * (scale n)⁻¹)‖ ^ 2)))
      atTop (nhds 0) := by
  have h₁ := h.tendsto_scaledGaussianNormDefect ht
  have h₂ := h.tendsto_scaledGaussianNormDefect (t := 2 * t)
    (mul_pos (show (0 : ℝ) < 2 by norm_num) ht)
  have h₂' : Tendsto
      (fun n : ℕ => (n : ℝ) *
        (1 - ‖charFun ν ((2 * t) * (scale n)⁻¹)‖ ^ 2))
      atTop (nhds ((2 * t) ^ (2 : ℝ))) := h₂
  have hlinear : Tendsto
      (fun n : ℕ => 4 * ((n : ℝ) *
          (1 - ‖charFun ν (t * (scale n)⁻¹)‖ ^ 2)) -
        ((n : ℝ) *
          (1 - ‖charFun ν ((2 * t) * (scale n)⁻¹)‖ ^ 2)))
      atTop (nhds (4 * t ^ (2 : ℝ) - (2 * t) ^ (2 : ℝ))) :=
    (h₁.const_mul 4).sub h₂'
  have hlimit : 4 * t ^ (2 : ℝ) - (2 * t) ^ (2 : ℝ) = 0 := by
    calc
      4 * t ^ (2 : ℝ) - (2 * t) ^ (2 : ℝ) = 4 * t ^ 2 - (2 * t) ^ 2 := by
        rw [Real.rpow_two, Real.rpow_two]
      _ = 0 := by ring
  have heq : (fun n : ℕ => (n : ℝ) *
        (4 * (1 - ‖charFun ν (t * (scale n)⁻¹)‖ ^ 2) -
          (1 - ‖charFun ν ((2 * t) * (scale n)⁻¹)‖ ^ 2))) =ᶠ[atTop]
      fun n => 4 * ((n : ℝ) *
          (1 - ‖charFun ν (t * (scale n)⁻¹)‖ ^ 2)) -
        ((n : ℝ) *
          (1 - ‖charFun ν ((2 * t) * (scale n)⁻¹)‖ ^ 2)) := by
    filter_upwards [] with n
    ring
  have hfinal := hlinear.congr' heq.symm
  rw [hlimit] at hfinal
  exact hfinal

/-- A centered probability law with positive second moment is in the
standard Gaussian domain of attraction along the canonical normalization
`sqrt (n * variance)`, with zero centering. -/
theorem isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_posSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : 0 < ∫ x, x ^ 2 ∂ν) :
    IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      (fun n => Real.sqrt ((n : ℝ) * ∫ x, x ^ 2 ∂ν)) (fun _ => 0) := by
  let secondMoment : ℝ := ∫ x, x ^ 2 ∂ν
  let sigma : ℝ := Real.sqrt secondMoment
  let normalization : ℕ → ℝ := fun n => Real.sqrt ((n : ℝ) * secondMoment)
  have hsquare : Integrable (fun x : ℝ => x ^ 2) ν :=
    Integrable.of_integral_ne_zero (ne_of_gt hsecondMoment)
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

/-- A centered probability law with second moment one belongs to the
standard Gaussian domain of attraction along the normalization `sqrt n`.
This is the unit-second-moment specialization of
`isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_posSecondMoment`.
The second-moment identity supplies the positive-integral hypothesis. -/
theorem isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_unitSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν) :
    IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      (fun n => Real.sqrt n) (fun _ => 0) := by
  have hsecondMoment : 0 < ∫ x, x ^ 2 ∂ν := by
    rw [hν.2]
    norm_num
  simpa [hν.2] using
    isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_posSecondMoment
      ν hν.1 hsecondMoment

/-- A centered probability law with positive second moment belongs to
the strictly `2`-stable domain of attraction of the standard Gaussian, with
the canonical second-moment normalization retained as a witness. -/
theorem isInAlphaStableDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_posSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : 0 < ∫ x, x ^ 2 ∂ν) :
    IsInAlphaStableDomainOfAttractionAlong 2 ν (gaussianReal 0 1)
      (fun n => Real.sqrt ((n : ℝ) * ∫ x, x ^ 2 ∂ν)) (fun _ => 0) := by
  refine ⟨(isStrictlyAlphaStable_gaussianReal_zero (by norm_num)).isAlphaStable, ?_⟩
  exact isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_posSecondMoment
    ν hcentered hsecondMoment

end ProbabilityTheory

end

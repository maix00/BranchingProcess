/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Moments.Variance
public import MeasureTheory.Measure.CharacteristicFunction.Convolution
public import Probability.Distributions.Stable.CharacteristicFunction
public import Probability.Distributions.Stable.Convolution
public import Probability.Sequence.IID.CharacteristicFunction

/-!
# Gaussian laws as stable laws

The centered Gaussian law is strictly stable with exponent two.  This file
connects mathlib's Gaussian distribution API to the abstract stable-law
predicate.  Small-deviation normalizations are handled in the Mogulskii
specialization layer.
-/

open Filter Topology MeasureTheory MeasureTheory.Measure ComplexConjugate
open scoped BigOperators NNReal

@[expose] public section

namespace ProbabilityTheory

theorem alphaStableScale_two_sq (a b : ℝ) :
    alphaStableScale 2 a b ^ 2 = a ^ 2 + b ^ 2 := by
  rw [alphaStableScale, Real.rpow_two, Real.rpow_two]
  rw [show (1 / (2 : ℝ)) = ((2 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.rpow_inv_natCast_pow (n := 2) (by positivity) (by norm_num)

theorem alphaStableScale_two_nonneg (a b : ℝ) :
    0 ≤ alphaStableScale 2 a b := by
  rw [alphaStableScale, Real.rpow_two, Real.rpow_two]
  exact Real.rpow_nonneg (by positivity) _

/-- Every nondegenerate centered real Gaussian probability law is strictly
`2`-stable. -/
theorem isStrictlyAlphaStable_gaussianReal_zero {v : ℝ≥0} (hv : v ≠ 0) :
    IsStrictlyAlphaStable 2 (gaussianReal 0 v) := by
  refine ⟨by norm_num, by norm_num, inferInstance, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    have hsingleton : gaussianReal 0 v {x} = 0 :=
      @NullSingletonClass.measure_singleton ℝ _ (gaussianReal 0 v)
        (nullSingletonClass_gaussianReal hv) x
    rw [hx] at hsingleton
    simp at hsingleton
  intro a b ha hb
  let μ := gaussianReal 0 v
  let X : ℝ × ℝ → ℝ := fun p => a * p.1
  let Y : ℝ × ℝ → ℝ := fun p => b * p.2
  have hX : HasLaw X
      (gaussianReal 0 (.mk (a ^ 2) (sq_nonneg a) * v)) (μ.prod μ) := by
    have hscale : HasLaw (fun x : ℝ => a * x)
        (gaussianReal 0 (.mk (a ^ 2) (sq_nonneg a) * v)) μ := by
      refine ⟨(measurable_const.mul measurable_id).aemeasurable, ?_⟩
      simpa using gaussianReal_map_const_mul (μ := 0) (v := v) a
    exact hscale.comp
      (measurePreserving_fst (μ := μ) (ν := μ)).hasLaw
  have hY : HasLaw Y
      (gaussianReal 0 (.mk (b ^ 2) (sq_nonneg b) * v)) (μ.prod μ) := by
    have hscale : HasLaw (fun x : ℝ => b * x)
        (gaussianReal 0 (.mk (b ^ 2) (sq_nonneg b) * v)) μ := by
      refine ⟨(measurable_const.mul measurable_id).aemeasurable, ?_⟩
      simpa using gaussianReal_map_const_mul (μ := 0) (v := v) b
    exact hscale.comp
      (measurePreserving_snd (μ := μ) (ν := μ)).hasLaw
  have hXY : IndepFun X Y (μ.prod μ) := by
    exact indepFun_prod (μ := μ) (ν := μ)
      (measurable_const.mul measurable_id)
      (measurable_const.mul measurable_id)
  have hadd := gaussianReal_add_gaussianReal_of_indepFun hXY hX hY
  have hleft : (μ.prod μ).map (weightedSum a b) =
      gaussianReal 0 ((.mk (a ^ 2) (sq_nonneg a) +
        .mk (b ^ 2) (sq_nonneg b)) * v) := by
    rw [show weightedSum a b = X + Y by
      funext p
      rfl]
    simpa only [zero_add, add_mul] using hadd
  rw [hleft]
  have hvariance :
      (.mk (a ^ 2) (sq_nonneg a) + .mk (b ^ 2) (sq_nonneg b)) =
        NNReal.mk (alphaStableScale 2 a b ^ 2)
          (sq_nonneg (alphaStableScale 2 a b)) := by
    apply NNReal.eq
    simp only [NNReal.coe_add, NNReal.coe_mk]
    exact (alphaStableScale_two_sq a b).symm
  rw [hvariance]
  symm
  simpa using gaussianReal_map_const_mul (μ := 0) (v := v)
    (alphaStableScale 2 a b)

private theorem memLp_id_two_of_gaussianDifference
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {v : ℝ≥0}
    (hD : (μ.prod μ).map (fun p : ℝ × ℝ => p.1 - p.2) =
      gaussianReal 0 v) : MemLp id 2 μ := by
  let d : ℝ × ℝ → ℝ := fun p => p.1 - p.2
  have hd : MemLp d 2 (μ.prod μ) := by
    have hG : MemLp id 2 ((μ.prod μ).map d) := by
      rw [hD]
      exact memLp_id_gaussianReal 2
    exact (memLp_map_measure_iff (p := 2)
      (stronglyMeasurable_id.aestronglyMeasurable)
      (by fun_prop : AEMeasurable d (μ.prod μ))).mp hG
  have hint : Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) (μ.prod μ) := by
    convert hd.integrable_sq using 1
  have hslice := (integrable_prod_iff' hint.aestronglyMeasurable).mp hint |>.1
  obtain ⟨y, hy⟩ := hslice.exists
  have hyInt : Integrable (fun x : ℝ => (x - y) ^ 2) μ := by
    simpa using hy
  have hdomInt : Integrable (fun x : ℝ => 2 * (x - y) ^ 2 + 2 * y ^ 2) μ := by
    exact (hyInt.const_mul 2).add (integrable_const (2 * y ^ 2))
  have hsqInt : Integrable (fun x : ℝ => x ^ 2) μ := by
    apply hdomInt.mono (by fun_prop)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x), Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (mul_nonneg (by norm_num) (sq_nonneg _)))]
    nlinarith [sq_nonneg (x - 2 * y)]
  exact (memLp_two_iff_integrable_sq (by fun_prop)).2 hsqInt

private theorem difference_gaussian_of_strictlyStable_two
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsStrictlyAlphaStable 2 μ) :
    ∃ v : ℝ≥0, v ≠ 0 ∧
      (μ.prod μ).map (fun p : ℝ × ℝ => p.1 - p.2) = gaussianReal 0 v := by
  let hA : IsAlphaStable 2 μ := h.isAlphaStable
  obtain ⟨c, hc, hmod⟩ := hA.exists_pos_norm_charFun_eq_exp
  let v : ℝ≥0 := ⟨4 * c, by positivity⟩
  have hv : v ≠ 0 := by
    intro hv
    have : (v : ℝ) = 0 := congrArg Subtype.val hv
    change 4 * c = 0 at this
    linarith
  let d : ℝ × ℝ → ℝ := fun p => p.1 - p.2
  have hprod : μ.prod (μ.map Neg.neg) = (μ.prod μ).map (Prod.map id Neg.neg) := by
    calc
      μ.prod (μ.map Neg.neg) = (μ.map id).prod (μ.map Neg.neg) := by simp
      _ = (μ.prod μ).map (Prod.map id Neg.neg) :=
        Measure.map_prod_map μ μ measurable_id measurable_neg
  have hconv : μ ∗ (μ.map Neg.neg) = (μ.prod μ).map d := by
    rw [Measure.conv, hprod, Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
  have hmapneg : μ.map Neg.neg = μ.map (fun x => (-1 : ℝ) * x) := by
    congr 1
    funext x
    ring
  have hcfneg (t : ℝ) : charFun (μ.map Neg.neg) t = conj (charFun μ t) := by
    rw [hmapneg, charFun_map_mul]
    simp
  have hchar (t : ℝ) : charFun ((μ.prod μ).map d) t =
      charFun (gaussianReal 0 v) t := by
    rw [← hconv, charFun_conv, hcfneg]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hmod t]
    have habs : |t| ^ (2 : ℝ) = t ^ 2 := by
      rw [Real.rpow_two]
      simp [pow_two]
    rw [habs]
    calc
      ↑(Real.exp (-c * t ^ 2) ^ 2) = Complex.exp ((2 : ℂ) * ((-c * t ^ 2 : ℝ) : ℂ)) := by
        simp only [Complex.ofReal_pow, Complex.ofReal_exp]
        rw [← Complex.exp_nat_mul]
        norm_num
      _ = charFun (gaussianReal 0 v) t := by
        rw [charFun_gaussianReal]
        congr 1
        have hvReal : (v : ℝ) = 4 * c := rfl
        rw [hvReal]
        push_cast
        ring
  exact ⟨v, hv, Measure.ext_of_charFun (funext hchar)⟩

private theorem strictlyStable_two_mean_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsStrictlyAlphaStable 2 μ) (hL2 : MemLp id 2 μ) :
    ∫ x, x ∂μ = 0 := by
  let m : ℝ := ∫ x, x ∂μ
  let s : ℝ := alphaStableScale 2 1 1
  have hsq : s ^ 2 = 2 := by
    calc
      s ^ 2 = alphaStableScale 2 1 1 ^ 2 := rfl
      _ = 1 ^ 2 + 1 ^ 2 := alphaStableScale_two_sq 1 1
      _ = 2 := by norm_num
  have hsne : s ≠ 2 := by
    intro hse
    rw [hse] at hsq
    norm_num at hsq
  have hstable : (μ.prod μ).map (fun p : ℝ × ℝ => p.1 + p.2) =
      μ.map (fun x : ℝ => s * x) := by
    have h := h.2.2.2.2 1 1 (by norm_num) (by norm_num)
    have hfun : weightedSum 1 1 = (fun p : ℝ × ℝ => p.1 + p.2) := by
      funext p
      simp [weightedSum]
    rw [hfun] at h
    simpa [s] using h
  have hIdInt : Integrable id μ := by
    have h1 : MemLp id 1 μ := hL2.mono_exponent (by norm_num)
    exact memLp_one_iff_integrable.mp h1
  have hfstInt : Integrable (fun p : ℝ × ℝ => p.1) (μ.prod μ) := by
    exact (measurePreserving_fst (μ := μ) (ν := μ)).integrable_comp_of_integrable hIdInt
  have hsndInt : Integrable (fun p : ℝ × ℝ => p.2) (μ.prod μ) := by
    exact (measurePreserving_snd (μ := μ) (ν := μ)).integrable_comp_of_integrable hIdInt
  have hleft : ∫ x, x ∂((μ.prod μ).map (fun p : ℝ × ℝ => p.1 + p.2)) =
      ∫ p, p.1 + p.2 ∂(μ.prod μ) := by
    rw [integral_map (by fun_prop) (by fun_prop)]
  have hright : ∫ x, x ∂(μ.map (fun x : ℝ => s * x)) =
      ∫ x, s * x ∂μ := by
    rw [integral_map (by fun_prop) (by fun_prop)]
  have hEqInt := congrArg (fun ρ : Measure ℝ => ∫ x, x ∂ρ) hstable
  rw [hleft, hright] at hEqInt
  have hfstMean : ∫ p : ℝ × ℝ, p.1 ∂(μ.prod μ) = m := by
    simpa [m, measure_univ] using
      (integral_fun_fst (μ := μ) (ν := μ) (f := id))
  have hsndMean : ∫ p : ℝ × ℝ, p.2 ∂(μ.prod μ) = m := by
    simpa [m, measure_univ] using
      (integral_fun_snd (μ := μ) (ν := μ) (f := id))
  have hsum : ∫ p : ℝ × ℝ, p.1 + p.2 ∂(μ.prod μ) = m + m := by
    calc
      _ = (∫ p : ℝ × ℝ, p.1 ∂(μ.prod μ)) + (∫ p : ℝ × ℝ, p.2 ∂(μ.prod μ)) :=
        integral_add hfstInt hsndInt
      _ = m + m := by rw [hfstMean, hsndMean]
  have hmul : ∫ x : ℝ, s * x ∂μ = s * m := by
    simpa [m] using (integral_const_mul s (id : ℝ → ℝ))
  rw [hsum, hmul] at hEqInt
  dsimp [m] at hEqInt ⊢
  have hmulzero : (2 - s) * (∫ x, x ∂μ) = 0 := by nlinarith
  rcases mul_eq_zero.mp hmulzero with hcoef | hmean
  · exact (hsne (by linarith)).elim
  · exact hmean

/-- Every nondegenerate strictly `2`-stable probability law on `ℝ` is a
centered Gaussian law with positive variance. The proof identifies the law
from the finite-variance central limit theorem and the stability identity. -/
theorem IsStrictlyAlphaStable.exists_gaussianReal_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsStrictlyAlphaStable 2 μ) :
    ∃ v : ℝ≥0, v ≠ 0 ∧ μ = gaussianReal 0 v := by
  obtain ⟨_, _, hD⟩ := difference_gaussian_of_strictlyStable_two h
  have hL2 : MemLp id 2 μ := memLp_id_two_of_gaussianDifference hD
  have hmean : ∫ x, x ∂μ = 0 := strictlyStable_two_mean_zero h hL2
  have hvarne : variance id μ ≠ 0 := by
    intro hvar
    have hconst := ae_eq_integral_of_variance_eq_zero hL2 hvar
    have hId : (fun x : ℝ => x) =ᵐ[μ] fun _ => μ[id] := by
      filter_upwards [hconst] with x hx
      exact hx
    have hmap : μ.map id = μ.map (fun _ : ℝ => μ[id]) :=
      Measure.map_congr hId
    have hdirac : μ = Measure.dirac (μ[id]) := by
      simpa [Measure.map_id, Measure.map_const, measure_univ] using hmap
    exact h.nondegenerate ⟨μ[id], hdirac⟩
  have hvarpos : 0 < variance id μ :=
    lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hvarne)
  let P := iidSequenceLaw μ
  let X : ℕ → (ℕ → ℝ) → ℝ := fun i sequence => sequence i
  have hXlaw (i : ℕ) : HasLaw (X i) μ P := by
    refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
    change P.map (fun sequence => sequence i) = μ
    exact iidSequenceLaw_map_apply μ i
  have hXid (i : ℕ) : IdentDistrib (X i) id P μ :=
    (hXlaw i).identDistrib HasLaw.id
  have hXmem : MemLp (X 0) 2 P := (hXid 0).memLp_iff.2 hL2
  have hXmean : P[X 0] = 0 := by
    rw [(hXid 0).integral_eq]
    exact hmean
  have hXvariance : variance (X 0) P = variance id μ := (hXlaw 0).variance_eq
  let Z : ℕ → (ℕ → ℝ) → ℝ := fun n sequence =>
    (Real.sqrt (n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, sequence k
  have hCLT : TendstoInDistribution Z atTop id (fun _ : ℕ => P)
      (gaussianReal 0 (variance id μ).toNNReal) := by
    have hCLT' := tendstoInDistribution_inv_sqrt_mul_sum_sub
      (P := P) (P' := gaussianReal 0 (variance (X 0) P).toNNReal)
      (X := X) (Y := id) HasLaw.id hXmem
      (iidSequenceLaw_independent μ) (fun i => (hXid i).trans (hXid 0).symm)
    simpa [Z, X, P, hXmean, hXvariance] using hCLT'
  have hsumLaw (n : ℕ) : P.map
      (fun sequence : ℕ → ℝ => ∑ k ∈ Finset.range n, sequence k) = μ.convPower n := by
    apply Measure.ext_of_charFun
    ext t
    rw [iidSequenceLaw_charFun_sum, Measure.charFun_convPower]
  have hsumNormalized (n : ℕ) (hn : 0 < n) : P.map (Z n) = μ := by
    have hscale : (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) ^ (1 / (2 : ℝ)) = 1 := by
      rw [← Real.sqrt_eq_rpow]
      exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hn)))
    change P.map ((fun x : ℝ => (Real.sqrt (n : ℝ))⁻¹ * x) ∘
      (fun sequence : ℕ → ℝ => ∑ k ∈ Finset.range n, sequence k)) = μ
    rw [← Measure.map_map (by fun_prop) (by fun_prop), hsumLaw,
      ← h.stableTimeLaw_nat n, stableTimeLaw]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have hcomp : ((fun x : ℝ => (Real.sqrt (n : ℝ))⁻¹ * x) ∘
        (fun x : ℝ => (n : ℝ) ^ (1 / (2 : ℝ)) * x)) = id := by
      funext x
      change (Real.sqrt (n : ℝ))⁻¹ * ((n : ℝ) ^ (1 / (2 : ℝ)) * x) = x
      calc
        _ = ((Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) ^ (1 / (2 : ℝ))) * x := by ring
        _ = 1 * x := by rw [hscale]
        _ = x := one_mul x
    rw [hcomp, Measure.map_id]
  let Zpos : ℕ → (ℕ → ℝ) → ℝ := fun n => Z (n + 1)
  have hCLTpos : TendstoInDistribution Zpos atTop id (fun _ : ℕ => P)
      (gaussianReal 0 (variance id μ).toNNReal) := by
    refine ⟨fun n => hCLT.forall_aemeasurable (n + 1), hCLT.aemeasurable_limit, ?_⟩
    have hfun :
        (fun n : ℕ => (⟨P.map (Zpos n), inferInstance⟩ : ProbabilityMeasure ℝ)) =
          (fun n : ℕ => (⟨P.map (Z n), inferInstance⟩ : ProbabilityMeasure ℝ)) ∘
            (fun n : ℕ => n + 1) := by
      funext n
      rfl
    rw [hfun]
    exact hCLT.tendsto.comp (tendsto_add_atTop_nat 1)
  have hZlaw (n : ℕ) : HasLaw (Zpos n) μ P := by
    refine ⟨?_, ?_⟩
    · fun_prop
    · change P.map (Z (n + 1)) = μ
      exact hsumNormalized (n + 1) (by omega)
  have hconst : TendstoInDistribution Zpos atTop id (fun _ : ℕ => P) μ := by
    apply tendstoInDistribution_of_identDistrib 0
    · intro n
      exact (hZlaw 0).identDistrib (hZlaw n)
    · exact (hZlaw 0).identDistrib HasLaw.id
  have hunique := tendstoInDistribution_unique Zpos hCLTpos hconst
  refine ⟨(variance id μ).toNNReal, (Real.toNNReal_pos.mpr hvarpos).ne', ?_⟩
  simpa [Measure.map_id] using hunique.symm

end ProbabilityTheory

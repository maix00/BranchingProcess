/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Analysis.Asymptotics.RegularVariation
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecificLimits.Basic
public import Probability.Distributions.CharacteristicFunction.Symmetrization.Tail

/-!
# Regular variation of symmetrized and original tails

For a probability law on the real line, the absolute tail of the difference
of two iid variables is asymptotic to twice the absolute tail of one variable
whenever the former is regularly varying with a negative index. The proof
uses product-measure rectangle bounds and does not assume a density.
-/

open Filter MeasureTheory Set
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

private theorem absBallMass_scaled_tendsto_one (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => absBallMass μ (c * x)) atTop (nhds 1) := by
  have htail := (twoSidedTail_tendsto_zero μ).comp
    (tendsto_id.const_mul_atTop hc)
  have heq : (fun x : ℝ => absBallMass μ (c * x)) =ᶠ[atTop]
      fun x => 1 - twoSidedTail μ (c * x) := by
    filter_upwards [] with x
    exact absBallMass_eq_one_sub_twoSidedTail μ (c * x)
  have htail' : Tendsto (fun x : ℝ => twoSidedTail μ (c * x)) atTop (nhds 0) := by
    simpa only [Function.comp_def, id_eq] using htail
  have hsub : Tendsto (fun x : ℝ => (1 : ℝ) - twoSidedTail μ (c * x))
      atTop (nhds 1) := by
    have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    simpa using hconst.sub htail'
  exact hsub.congr' heq.symm

/-- Regular variation of the absolute tail of the symmetrized law transfers
to the original absolute tail. The ratio limit is one half; this is the
probability-level symmetrization step needed after the inverse cosine
Tauberian theorem. -/
theorem twoSidedTail_div_symmetrized_tendsto_half
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hS : Asymptotics.IsRegularlyVaryingAtTop
      (twoSidedTail (symmetrizedMeasure μ)) (-α)) :
    Tendsto (fun x : ℝ => twoSidedTail μ x /
      twoSidedTail (symmetrizedMeasure μ) x) atTop (nhds (1 / 2 : ℝ)) := by
  let T : ℝ → ℝ := twoSidedTail μ
  let S : ℝ → ℝ := twoSidedTail (symmetrizedMeasure μ)
  let R : ℝ → ℝ := fun x => T x / S x
  have hsymProb : IsProbabilityMeasure (symmetrizedMeasure μ) := by
    dsimp [symmetrizedMeasure]
    infer_instance
  have hTzero : Tendsto T atTop (nhds 0) := twoSidedTail_tendsto_zero μ
  have hSzero : Tendsto S atTop (nhds 0) :=
    @twoSidedTail_tendsto_zero (symmetrizedMeasure μ) hsymProb
  have hSpos : ∀ᶠ x : ℝ in atTop, 0 < S x := hS.eventually_pos
  let en : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hen : Tendsto en atTop (nhds 0) := by
    simpa [en] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hplusCont : ContinuousAt (fun e : ℝ => (1 + e) ^ α) 0 := by
    have hpow : ContinuousAt (fun z : ℝ => z ^ α) 1 :=
      Real.continuousAt_rpow_const 1 α (Or.inl one_ne_zero)
    have hpow' : ContinuousAt (fun z : ℝ => z ^ α) (1 + 0) := by
      simpa using hpow
    have hlin : ContinuousAt (fun e : ℝ => 1 + e) 0 := by fun_prop
    simpa only [Function.comp_def] using
      ContinuousAt.comp (f := fun e : ℝ => 1 + e) (x := 0)
        (g := fun z : ℝ => z ^ α) hpow' hlin
  have hminusCont : ContinuousAt (fun e : ℝ => (1 - e) ^ α) 0 := by
    have hpow : ContinuousAt (fun z : ℝ => z ^ α) 1 :=
      Real.continuousAt_rpow_const 1 α (Or.inl one_ne_zero)
    have hpow' : ContinuousAt (fun z : ℝ => z ^ α) (1 - 0) := by
      simpa using hpow
    have hlin : ContinuousAt (fun e : ℝ => 1 - e) 0 := by fun_prop
    simpa only [Function.comp_def] using
      ContinuousAt.comp (f := fun e : ℝ => 1 - e) (x := 0)
        (g := fun z : ℝ => z ^ α) hpow' hlin
  have hplusSeq : Tendsto (fun n : ℕ => (1 + en n) ^ α) atTop (nhds 1) := by
    simpa [Function.comp_def, Real.one_rpow] using hplusCont.tendsto.comp hen
  have hminusSeq : Tendsto (fun n : ℕ => (1 - en n) ^ α) atTop (nhds 1) := by
    simpa [Function.comp_def, Real.one_rpow] using hminusCont.tendsto.comp hen
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  have hplusEvent : ∀ᶠ n : ℕ in atTop,
      |(1 + en n) ^ α - 1| < ε / 4 := by
    have h := hplusSeq.eventually (Metric.ball_mem_nhds 1 hε4)
    filter_upwards [h] with n hn
    simpa only [Real.dist_eq] using hn
  have hminusEvent : ∀ᶠ n : ℕ in atTop,
      |(1 - en n) ^ α - 1| < ε / 4 := by
    have h := hminusSeq.eventually (Metric.ball_mem_nhds 1 hε4)
    filter_upwards [h] with n hn
    simpa only [Real.dist_eq] using hn
  have hnEvent : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  obtain ⟨n, hn⟩ := ((hplusEvent.and hminusEvent).and hnEvent).exists
  rcases hn with ⟨⟨hnplus, hnminus⟩, hn⟩
  let e : ℝ := en n
  have hepos : 0 < e := by
    dsimp [e, en]
    positivity
  have helt : e < 1 := by
    dsimp [e, en]
    have hn' : 1 < n + 1 := by omega
    have hden : (1 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast hn'
    apply (div_lt_one (by positivity)).2
    exact_mod_cast hden
  have hplusClose : |(1 + e) ^ α / 2 - (1 / 2 : ℝ)| < ε / 8 := by
    have heq : (1 + e) ^ α / 2 - (1 / 2 : ℝ) = ((1 + en n) ^ α - 1) / 2 := by
      dsimp [e]
      ring
    rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hminusClose : |(1 - e) ^ α / 2 - (1 / 2 : ℝ)| < ε / 8 := by
    have heq : (1 - e) ^ α / 2 - (1 / 2 : ℝ) = ((1 - en n) ^ α - 1) / 2 := by
      dsimp [e]
      ring
    rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  let cU : ℝ := (1 + e)⁻¹
  let cUF : ℝ := e * cU
  let cL : ℝ := (1 - e)⁻¹
  let cLF : ℝ := e * cL
  have hcU : 0 < cU := by dsimp [cU]; positivity
  have hcUF : 0 < cUF := by dsimp [cUF]; positivity
  have hcL : 0 < cL := by dsimp [cL]; positivity
  have hcLF : 0 < cLF := by dsimp [cLF]; positivity
  let Ufun : ℝ → ℝ := fun x =>
    (S (cU * x) / S x / absBallMass μ (cUF * x)) / 2
  let small : ℝ → ℝ := fun x => T (cLF * x) ^ 2 / S x
  let Lfun : ℝ → ℝ := fun x => (S (cL * x) / S x - small x) / 2
  have hmassU : Tendsto (fun x : ℝ => absBallMass μ (cUF * x)) atTop (nhds 1) :=
    absBallMass_scaled_tendsto_one μ hcUF
  have hmassL : Tendsto (fun x : ℝ => absBallMass μ (cLF * x)) atTop (nhds 1) :=
    absBallMass_scaled_tendsto_one μ hcLF
  have hmassSmall : Tendsto (fun x : ℝ => absBallMass μ ((cLF / 2) * x)) atTop
      (nhds 1) := absBallMass_scaled_tendsto_one μ (by positivity)
  have hUlim : Tendsto Ufun atTop (nhds (cU ^ (-α) / 2)) := by
    have hratio := hS.ratio_tendsto hcU
    have hratioMass := hratio.div hmassU (by norm_num : (1 : ℝ) ≠ 0)
    have h := hratioMass.div_const 2
    simpa [Ufun, S] using h
  have hcUpow : cU ^ (-α) = (1 + e) ^ α := by
    dsimp [cU]
    rw [Real.inv_rpow (by positivity : 0 ≤ (1 + e : ℝ)),
      Real.rpow_neg (by positivity : 0 ≤ (1 + e : ℝ))]
    simp
  have hUlim' : Tendsto Ufun atTop (nhds ((1 + e) ^ α / 2)) := by
    simpa [hcUpow] using hUlim
  have hUtarget : cU ^ (-α) / 2 < 1 / 2 + ε := by
    rw [hcUpow]
    have h := abs_lt.mp hplusClose
    linarith
  have hUevent : ∀ᶠ x : ℝ in atTop, Ufun x < 1 / 2 + ε :=
    hUlim'.eventually (isOpen_Iio.mem_nhds (by rw [← hcUpow]; exact hUtarget))
  have hTsmall : Tendsto (fun x : ℝ => T (cLF * x)) atTop (nhds 0) :=
    hTzero.comp (tendsto_id.const_mul_atTop hcLF)
  have hSsmall : Tendsto (fun x : ℝ => S ((cLF / 2) * x)) atTop (nhds 0) :=
    hSzero.comp (tendsto_id.const_mul_atTop (by positivity))
  have hSratioSmall : Tendsto (fun x : ℝ =>
      S ((cLF / 2) * x) / S x) atTop (nhds ((cLF / 2) ^ (-α))) :=
    hS.ratio_tendsto (by positivity)
  have hmajor : Tendsto (fun x : ℝ =>
      (S ((cLF / 2) * x) / S x) * S ((cLF / 2) * x)) atTop (nhds 0) := by
    have h := hSratioSmall.mul hSsmall
    simpa using h
  have hsmallNonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ small x := by
    filter_upwards [hSpos] with x hx
    exact div_nonneg (sq_nonneg _) hx.le
  have hsmallLe : ∀ᶠ x : ℝ in atTop,
      small x ≤ (S ((cLF / 2) * x) / S x) * S ((cLF / 2) * x) := by
    have hball : ∀ᶠ x : ℝ in atTop,
        1 / 2 < absBallMass μ ((cLF / 2) * x) :=
      hmassSmall.eventually (isOpen_Ioi.mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
    filter_upwards [eventually_gt_atTop (0 : ℝ), hSpos, hball] with x hx hxS hball
    have hz : 0 < (cLF / 2) * x := mul_pos (by positivity) hx
    have hstep := twoSidedTail_symmetrized_lower_bound (μ := μ) hz
      (by norm_num : (0 : ℝ) < 1)
    have harg₁ : (1 + 1) * ((cLF / 2) * x) = cLF * x := by ring
    have harg₂ : 1 * ((cLF / 2) * x) = (cLF / 2) * x := by ring
    rw [harg₁, harg₂] at hstep
    have hstep' : 2 * T (cLF * x) * absBallMass μ ((cLF / 2) * x) ≤
        S ((cLF / 2) * x) := by
      simpa [T, S, absBallMass] using hstep
    have hTle : T (cLF * x) ≤ S ((cLF / 2) * x) := by
      have hTnonneg : 0 ≤ T (cLF * x) := by
        exact measureReal_nonneg
      nlinarith [hstep', hTnonneg]
    have hsq : T (cLF * x) ^ 2 ≤ S ((cLF / 2) * x) ^ 2 := by
      have hTnonneg : 0 ≤ T (cLF * x) := measureReal_nonneg
      have hSnonneg : 0 ≤ S ((cLF / 2) * x) := measureReal_nonneg
      have hdiff : 0 ≤ S ((cLF / 2) * x) - T (cLF * x) := sub_nonneg.mpr hTle
      have hsum : 0 ≤ S ((cLF / 2) * x) + T (cLF * x) :=
        add_nonneg hSnonneg hTnonneg
      nlinarith [mul_nonneg hdiff hsum]
    have hdiv : T (cLF * x) ^ 2 / S x ≤
        (S ((cLF / 2) * x) / S x) * S ((cLF / 2) * x) := by
      calc
        T (cLF * x) ^ 2 / S x ≤ S ((cLF / 2) * x) ^ 2 / S x :=
          div_le_div_of_nonneg_right hsq hxS.le
        _ = (S ((cLF / 2) * x) / S x) * S ((cLF / 2) * x) := by
          field_simp [ne_of_gt hxS]
    have heq : S ((cLF / 2) * x) ^ 2 / S x =
        (S ((cLF / 2) * x) / S x) * S ((cLF / 2) * x) := by
      field_simp [ne_of_gt hxS]
    simpa [small] using hdiv
  have hsmallLimit : Tendsto small atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hmajor hsmallNonneg hsmallLe
  have hLlim : Tendsto Lfun atTop (nhds (cL ^ (-α) / 2)) := by
    have hratio := hS.ratio_tendsto hcL
    have h := (hratio.sub hsmallLimit).div_const 2
    simpa [Lfun] using h
  have hcLpow : cL ^ (-α) = (1 - e) ^ α := by
    dsimp [cL]
    rw [Real.inv_rpow (by linarith : 0 ≤ (1 - e : ℝ)),
      Real.rpow_neg (by linarith : 0 ≤ (1 - e : ℝ))]
    simp
  have hLlim' : Tendsto Lfun atTop (nhds ((1 - e) ^ α / 2)) := by
    simpa [hcLpow] using hLlim
  have hLtarget : 1 / 2 - ε < cL ^ (-α) / 2 := by
    rw [hcLpow]
    have h := abs_lt.mp hminusClose
    linarith
  have hLevent : ∀ᶠ x : ℝ in atTop, 1 / 2 - ε < Lfun x :=
    hLlim.eventually (isOpen_Ioi.mem_nhds hLtarget)
  have hUbound : ∀ᶠ x : ℝ in atTop, R x ≤ Ufun x := by
    have hmass : ∀ᶠ x : ℝ in atTop, 0 < absBallMass μ (cUF * x) :=
      hmassU.eventually (isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [eventually_gt_atTop (0 : ℝ), hSpos, hmass] with x hx hxS hmass
    have hz : 0 < cU * x := mul_pos hcU hx
    have hstep := twoSidedTail_symmetrized_lower_bound (μ := μ) hz hepos
    have harg₁ : (1 + e) * (cU * x) = x := by
      dsimp [cU]
      field_simp
    have harg₂ : e * (cU * x) = cUF * x := by
      dsimp [cU, cUF]
      ring
    rw [harg₁, harg₂] at hstep
    have hstep' : 2 * T x * absBallMass μ (cUF * x) ≤ S (cU * x) := by
      simpa [T, S, absBallMass] using hstep
    have hcross : T x * (2 * absBallMass μ (cUF * x) * S x) ≤
        S (cU * x) * S x := by
      calc
        T x * (2 * absBallMass μ (cUF * x) * S x) =
            (2 * T x * absBallMass μ (cUF * x)) * S x := by ring
        _ ≤ S (cU * x) * S x := mul_le_mul_of_nonneg_right hstep' hxS.le
    have hdiv := (div_le_div_iff₀ hxS
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hmass) hxS)).2 hcross
    have heq : S (cU * x) / (2 * absBallMass μ (cUF * x) * S x) = Ufun x := by
      dsimp [Ufun]
      field_simp
    simpa [R, heq] using hdiv
  have hLbound : ∀ᶠ x : ℝ in atTop, Lfun x ≤ R x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hSpos] with x hx hxS
    have hz : 0 < cL * x := mul_pos hcL hx
    have hstep := twoSidedTail_symmetrized_upper_bound (μ := μ) hz hepos helt
    have harg₁ : (1 - e) * (cL * x) = x := by
      dsimp [cL]
      field_simp [ne_of_gt (by linarith : 0 < (1 - e : ℝ))]
    have harg₂ : e * (cL * x) = cLF * x := by
      dsimp [cL, cLF]
      ring
    rw [harg₁, harg₂] at hstep
    have hstep' : S (cL * x) ≤ 2 * T x + T (cLF * x) ^ 2 := by
      simpa [T, S] using hstep
    have hdiv : S (cL * x) / S x ≤
        (2 * T x + T (cLF * x) ^ 2) / S x :=
      div_le_div_of_nonneg_right hstep' hxS.le
    have hgoal : (S (cL * x) / S x - T (cLF * x) ^ 2 / S x) / 2 ≤ T x / S x := by
      field_simp [ne_of_gt hxS] at hdiv ⊢
      nlinarith
    simpa [Lfun, small, R] using hgoal
  have hUpperLim : cU ^ (-α) / 2 < 1 / 2 + ε := hUtarget
  have hLowerLim : 1 / 2 - ε < cL ^ (-α) / 2 := hLtarget
  have hupperEvent : ∀ᶠ x : ℝ in atTop, Ufun x < 1 / 2 + ε :=
    hUlim'.eventually (isOpen_Iio.mem_nhds (by rw [← hcUpow]; exact hUpperLim))
  have hlowerEvent : ∀ᶠ x : ℝ in atTop, 1 / 2 - ε < Lfun x :=
    hLlim'.eventually (isOpen_Ioi.mem_nhds (by rw [← hcLpow]; exact hLowerLim))
  have hclose : ∀ᶠ x : ℝ in atTop, dist (R x) (1 / 2) < ε := by
    filter_upwards [hUbound, hLbound, hupperEvent, hlowerEvent] with x hu hl hU hL
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> linarith
  simpa [R, T, S] using hclose

/-- Regular variation of the symmetrized two-sided tail transfers to the
original law's two-sided tail. This uses the ratio limit above and does not
assume regular variation of the original tail. -/
theorem twoSidedTail_isRegularlyVarying_of_symmetrized
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hS : Asymptotics.IsRegularlyVaryingAtTop
      (twoSidedTail (symmetrizedMeasure μ)) (-α)) :
    Asymptotics.IsRegularlyVaryingAtTop (twoSidedTail μ) (-α) := by
  let T : ℝ → ℝ := twoSidedTail μ
  let S : ℝ → ℝ := twoSidedTail (symmetrizedMeasure μ)
  let R : ℝ → ℝ := fun x => T x / S x
  have hsymProb : IsProbabilityMeasure (symmetrizedMeasure μ) := by
    dsimp [symmetrizedMeasure]
    infer_instance
  have hratio : Tendsto R atTop (nhds (1 / 2 : ℝ)) := by
    simpa [R, T, S] using
      twoSidedTail_div_symmetrized_tendsto_half (μ := μ) (α := α) hS
  have hSpos : ∀ᶠ x : ℝ in atTop, 0 < S x := hS.eventually_pos
  have hTpos : ∀ᶠ x : ℝ in atTop, 0 < T x := by
    have hRpos : ∀ᶠ x : ℝ in atTop, 0 < R x :=
      hratio.eventually (isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hSpos, hRpos] with x hxS hxR
    have hdiv : 0 < T x / S x := by simpa [R] using hxR
    exact (div_pos_iff_of_pos_right hxS).mp hdiv
  refine ⟨hTpos, ?_⟩
  intro c hc
  have hcTop : Tendsto (fun x : ℝ => c * x) atTop atTop :=
    tendsto_id.const_mul_atTop hc
  have hratioScaled : Tendsto (fun x : ℝ => R (c * x)) atTop
      (nhds (1 / 2 : ℝ)) := hratio.comp hcTop
  have hquot : Tendsto (fun x : ℝ => R (c * x) / R x) atTop (nhds 1) := by
    have hquot' : Tendsto ((fun x : ℝ => R (c * x)) / R) atTop
        (nhds ((1 / 2 : ℝ) / (1 / 2 : ℝ))) :=
      hratioScaled.div hratio (by norm_num : (1 / 2 : ℝ) ≠ 0)
    have heq : ((fun x : ℝ => R (c * x)) / R) =
        (fun x => R (c * x) / R x) := by
      funext x
      rfl
    rw [heq] at hquot'
    simpa using hquot'
  have hproduct := hquot.mul (hS.ratio_tendsto hc)
  have hSscaledPos : ∀ᶠ x : ℝ in atTop, 0 < S (c * x) := hcTop.eventually hSpos
  have heq : (fun x : ℝ => T (c * x) / T x) =ᶠ[atTop]
      fun x => (R (c * x) / R x) * (S (c * x) / S x) := by
    filter_upwards [hSscaledPos, hSpos, hTpos] with x hxSc hxS hxT
    simp only [R]
    field_simp [ne_of_gt hxSc, ne_of_gt hxS, ne_of_gt hxT]
  simpa [T, S] using hproduct.congr' heq.symm

end ProbabilityTheory

end

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

module

public import Analysis.Asymptotics.RegularVariation
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Real
public import Probability.Distributions.Moments.Truncated

/-!
# Regular variation of truncated second moments

This file derives negligibility of the quadratic two-sided tail from slow
variation of the truncated second moment and records its fixed-scale consequence.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

private theorem truncatedSecondMoment_band_lower_bound
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    a ^ 2 * μ.real {y : ℝ | a < |y| ∧ |y| ≤ b} ≤
      truncatedSecondMoment μ b - truncatedSecondMoment μ a := by
  let outer : Set ℝ := Set.Icc (-b) b
  let inner : Set ℝ := Set.Icc (-a) a
  let band : Set ℝ := outer \ inner
  have hb : 0 ≤ b := le_trans ha hab
  have houterBound : ∀ y ∈ outer, ‖y ^ 2‖ ≤ b ^ 2 := by
    intro y hy
    have hyabs : |y| ≤ b := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
    have hsq : y ^ 2 ≤ b ^ 2 := by
      rw [← sq_abs y]
      exact (sq_le_sq₀ (abs_nonneg y) hb).2 hyabs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg y)]
    exact hsq
  have houterInt : IntegrableOn (fun y : ℝ => y ^ 2) outer μ :=
    Measure.integrableOn_of_bounded (measure_ne_top μ outer)
      (by fun_prop : AEStronglyMeasurable (fun y : ℝ => y ^ 2) μ)
      (ae_restrict_of_forall_mem measurableSet_Icc houterBound)
  have hinnerSub : inner ⊆ outer := by
    intro y hy
    exact ⟨(neg_le_neg hab).trans hy.1, hy.2.trans hab⟩
  have hdiff : ∫ y in band, y ^ 2 ∂μ =
      truncatedSecondMoment μ b - truncatedSecondMoment μ a := by
    rw [show band = outer \ inner by rfl,
      setIntegral_sdiff measurableSet_Icc houterInt hinnerSub]
    rfl
  have hband : band = {y : ℝ | a < |y| ∧ |y| ≤ b} := by
    ext y
    simp only [band, outer, inner, Set.mem_sdiff, Set.mem_Icc, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hy₁, hy₂⟩, hnot⟩
      have hyabs : |y| ≤ b := abs_le.mpr ⟨by linarith [hy₁], hy₂⟩
      have hya : a < |y| := by
        by_contra h
        have hya' : |y| ≤ a := le_of_not_gt h
        exact hnot (abs_le.mp hya')
      exact ⟨hya, hyabs⟩
    · rintro ⟨hya, hyb⟩
      have hyb' := abs_le.mp hyb
      refine ⟨⟨hyb'.1, hyb'.2⟩, ?_⟩
      intro hy
      have hya' : |y| ≤ a := abs_le.mpr hy
      exact (not_le_of_gt hya) hya'
  have hbandMeas : MeasurableSet band := by
    dsimp [band]
    exact measurableSet_Icc.diff measurableSet_Icc
  have hbandInt : IntegrableOn (fun y : ℝ => y ^ 2) band μ :=
    houterInt.mono_set Set.sdiff_subset
  have hconstInt : IntegrableOn (fun _ : ℝ => a ^ 2) band μ :=
    integrableOn_const (C := a ^ 2) (μ := μ) (s := band) (measure_ne_top μ band)
  have hpoint : ∀ y ∈ band, a ^ 2 ≤ y ^ 2 := by
    intro y hy
    rw [hband] at hy
    calc
      a ^ 2 ≤ |y| ^ 2 := (sq_le_sq₀ ha (abs_nonneg y)).2 hy.1.le
      _ = y ^ 2 := sq_abs y
  have hlow := setIntegral_mono_on hconstInt hbandInt hbandMeas hpoint
  have hlow' : a ^ 2 * μ.real band ≤ ∫ y in band, y ^ 2 ∂μ := by
    simpa [setIntegral_const, smul_eq_mul, mul_comm] using hlow
  calc
    a ^ 2 * μ.real {y : ℝ | a < |y| ∧ |y| ≤ b} = a ^ 2 * μ.real band := by
      rw [← hband]
    _ ≤ ∫ y in band, y ^ 2 ∂μ := hlow'
    _ = truncatedSecondMoment μ b - truncatedSecondMoment μ a := hdiff

private theorem twoSidedTail_difference_eq_band
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ}
    (hab : a ≤ b) :
    μ.real {y : ℝ | a < |y|} - μ.real {y : ℝ | b < |y|} =
      μ.real {y : ℝ | a < |y| ∧ |y| ≤ b} := by
  have hsubset : {y : ℝ | b < |y|} ⊆ {y | a < |y|} := by
    intro y hy
    exact lt_of_le_of_lt hab hy
  have hset : {y : ℝ | a < |y|} \ {y : ℝ | b < |y|} =
      {y : ℝ | a < |y| ∧ |y| ≤ b} := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hya, hyb⟩
      exact ⟨hya, le_of_not_gt hyb⟩
    · rintro ⟨hya, hyb⟩
      exact ⟨hya, not_lt.mpr hyb⟩
  rw [← hset]
  exact (measureReal_sdiff (μ := μ) hsubset
    (measurableSet_lt measurable_const continuous_abs.measurable) (measure_ne_top μ _)).symm

private theorem twoSidedTail_difference_mul_sq_le_truncatedSecondMoment_difference
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    a ^ 2 * (μ.real {y : ℝ | a < |y|} - μ.real {y : ℝ | b < |y|}) ≤
      truncatedSecondMoment μ b - truncatedSecondMoment μ a := by
  rw [twoSidedTail_difference_eq_band μ hab]
  exact truncatedSecondMoment_band_lower_bound μ ha hab

/-- If the truncated second moment is slowly varying and the two-sided tail
is negligible after multiplication by `x²`, then it is still negligible at
any fixed positive rescaling of the cutoff, relative to the original
truncated second moment. -/
theorem tendsto_rescaledSecondTailRatio_of_slowVariation
    (μ : Measure ℝ)
    (hVslow : Asymptotics.IsSlowlyVaryingAtTop (truncatedSecondMoment μ))
    (hTail : Tendsto
      (fun x : ℝ => x ^ 2 * μ.real {y : ℝ | x < |y|} /
        truncatedSecondMoment μ x) atTop (nhds 0))
    (c : ℝ) (hc : 0 < c) :
    Tendsto
      (fun x : ℝ => x ^ 2 * μ.real {y : ℝ | c * x < |y|} /
        truncatedSecondMoment μ x)
      atTop (nhds 0) := by
  let V : ℝ → ℝ := truncatedSecondMoment μ
  let tail : ℝ → ℝ := fun x => μ.real {y : ℝ | x < |y|}
  have hVscale : Tendsto (fun x : ℝ => V (c * x) / V x) atTop (nhds 1) := by
    simpa [V, Real.rpow_zero] using hVslow.ratio_tendsto hc
  have htailScale : Tendsto
      (fun x : ℝ => (c * x) ^ 2 * tail (c * x) / V (c * x))
      atTop (nhds 0) := by
    have hscale : Tendsto (fun x : ℝ => c * x) atTop atTop :=
      tendsto_id.const_mul_atTop hc
    exact hTail.comp hscale
  have hprod := htailScale.mul hVscale
  have hconst := hprod.const_mul (c⁻¹ ^ 2)
  have hVcx : ∀ᶠ x : ℝ in atTop, 0 < V (c * x) := by
    exact (tendsto_id.const_mul_atTop hc).eventually hVslow.eventually_pos
  have heq : (fun x : ℝ => c⁻¹ ^ 2 *
      ((c * x) ^ 2 * tail (c * x) / V (c * x) *
        (V (c * x) / V x))) =ᶠ[atTop]
      fun x => x ^ 2 * tail (c * x) / V x := by
    filter_upwards [hVcx] with x hx
    field_simp [ne_of_gt hc, ne_of_gt hx]
  have hconst' : Tendsto
      (fun x : ℝ => c⁻¹ ^ 2 *
        ((c * x) ^ 2 * tail (c * x) / V (c * x) *
          (V (c * x) / V x))) atTop (nhds 0) := by
    simpa using hconst
  have hresult := hconst'.congr' heq
  simpa [V, tail] using hresult

/-- Slow variation of the truncated second moment forces the quadratic tail
to be negligible. The proof decomposes the tail into dyadic bands, bounds each
band by the increment of the truncated moment, and uses Potter domination to
pass the limit through the resulting series. Only finiteness of the measure
is needed; no global second moment is assumed. -/
theorem tendsto_secondTailRatio_of_slowlyVarying_truncatedSecondMoment
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hVslow : Asymptotics.IsSlowlyVaryingAtTop (truncatedSecondMoment μ)) :
    Tendsto
      (fun x : ℝ => x ^ 2 * μ.real {y : ℝ | x < |y|} /
        truncatedSecondMoment μ x)
      atTop (nhds 0) := by
  let V : ℝ → ℝ := truncatedSecondMoment μ
  let tail : ℝ → ℝ := fun x => μ.real {y : ℝ | x < |y|}
  let term : ℝ → ℕ → ℝ := fun x k =>
    ((4 : ℝ) ^ k)⁻¹ *
      (V ((2 : ℝ) ^ (k + 1) * x) / V x - V ((2 : ℝ) ^ k * x) / V x)
  have hVreg : Asymptotics.IsRegularlyVaryingAtTop V 0 := hVslow
  have hVmono : Asymptotics.IsEventuallyMonotoneAtTop V := by
    refine ⟨0, ?_⟩
    intro x y hx hxy
    exact truncatedSecondMoment_mono μ hx hxy
  obtain ⟨R, _, hpotter⟩ :=
    hVreg.exists_potter_upper_bound hVmono (by norm_num : (0 : ℝ) ≤ 0)
      (by norm_num : (0 : ℝ) < 1)
  have hVpos : ∀ᶠ x : ℝ in atTop, 0 < V x := hVslow.eventually_pos
  have htermPoint : ∀ k : ℕ, Tendsto (fun x : ℝ => term x k) atTop (nhds 0) := by
    intro k
    have hc₀ : 0 < (2 : ℝ) ^ k := by positivity
    have hc₁ : 0 < (2 : ℝ) ^ (k + 1) := by positivity
    have hratio₀ : Tendsto (fun x : ℝ => V ((2 : ℝ) ^ k * x) / V x)
        atTop (nhds 1) := by
      simpa [V, Real.rpow_zero] using hVslow.ratio_tendsto hc₀
    have hratio₁ : Tendsto (fun x : ℝ => V ((2 : ℝ) ^ (k + 1) * x) / V x)
        atTop (nhds 1) := by
      simpa [V, Real.rpow_zero] using hVslow.ratio_tendsto hc₁
    have hdiff := hratio₁.sub hratio₀
    simpa [term] using hdiff.const_mul (((4 : ℝ) ^ k)⁻¹)
  have htermBound : ∀ᶠ x : ℝ in atTop,
      ∀ k : ℕ, ‖term x k‖ ≤ 4 * (1 / 2 : ℝ) ^ k := by
    filter_upwards [eventually_ge_atTop R, hVpos, eventually_gt_atTop (0 : ℝ)]
      with x hxR hVx hx
    intro k
    let c₀ : ℝ := (2 : ℝ) ^ k * x
    let c₁ : ℝ := (2 : ℝ) ^ (k + 1) * x
    have hpow₀ : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    have hpow₁ : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) := by
      rw [pow_succ]
      nlinarith [hpow₀]
    have hxc₁ : x ≤ c₁ := by dsimp [c₁]; nlinarith
    have hV0 : 0 ≤ V c₀ := by
      dsimp [V, truncatedSecondMoment]
      exact setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _
    have hV01 : V c₀ ≤ V c₁ := by
      apply truncatedSecondMoment_mono μ
      · exact mul_nonneg (pow_nonneg (by norm_num) _) hx.le
      · exact mul_le_mul_of_nonneg_right hpow₁ hx.le
    have hratio₀ : 0 ≤ V c₀ / V x := div_nonneg hV0 hVx.le
    have hratioDiff : 0 ≤ V c₁ / V x - V c₀ / V x :=
      sub_nonneg.mpr (div_le_div_of_nonneg_right hV01 hVx.le)
    have hweight : 0 < ((4 : ℝ) ^ k)⁻¹ := inv_pos.mpr (pow_pos (by norm_num) _)
    have htermNonneg : 0 ≤ term x k := by
      exact mul_nonneg hweight.le hratioDiff
    have hpotter₁ := hpotter hxR hxc₁
    have hc₁div : c₁ / x = (2 : ℝ) ^ (k + 1) := by
      dsimp [c₁]
      field_simp [hx.ne']
    have hratio₁ : V c₁ / V x ≤ 2 * (2 : ℝ) ^ (k + 1) := by
      calc
        V c₁ / V x ≤ 2 ^ (0 + 1) * (c₁ / x) ^ (0 + 1) := hpotter₁
        _ = 2 * (2 : ℝ) ^ (k + 1) := by rw [hc₁div]; norm_num
    have htermLe : term x k ≤ ((4 : ℝ) ^ k)⁻¹ * (2 * (2 : ℝ) ^ (k + 1)) := by
      dsimp [term]
      calc
        ((4 : ℝ) ^ k)⁻¹ *
            (V c₁ / V x - V c₀ / V x) ≤
          ((4 : ℝ) ^ k)⁻¹ * (V c₁ / V x) :=
            mul_le_mul_of_nonneg_left (sub_le_self _ hratio₀) hweight.le
        _ ≤ ((4 : ℝ) ^ k)⁻¹ * (2 * (2 : ℝ) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left hratio₁ hweight.le
    have hcoefficient :
        ((4 : ℝ) ^ k)⁻¹ * (2 * (2 : ℝ) ^ (k + 1)) =
          4 * (1 / 2 : ℝ) ^ k := by
      calc
        ((4 : ℝ) ^ k)⁻¹ * (2 * (2 : ℝ) ^ (k + 1)) =
            4 * ((2 : ℝ) ^ k / (4 : ℝ) ^ k) := by
          rw [pow_succ]
          field_simp [pow_ne_zero k (by norm_num : (4 : ℝ) ≠ 0)]
          ring
        _ = 4 * (1 / 2 : ℝ) ^ k := by
          rw [← div_pow]
          norm_num
    have htermLe' := htermLe.trans_eq hcoefficient
    simpa [Real.norm_of_nonneg htermNonneg] using htermLe'
  have hgeometric : Summable (fun k : ℕ => 4 * (1 / 2 : ℝ) ^ k) := by
    simpa using (summable_geometric_two.mul_left (4 : ℝ))
  have hsum : Tendsto (fun x : ℝ => ∑' k : ℕ, term x k) atTop (nhds 0) := by
    simpa [term] using
      (tendsto_tsum_of_dominated_convergence hgeometric htermPoint htermBound)

  have htailToZero : ∀ x : ℝ, 0 < x →
      Tendsto (fun N : ℕ => tail ((2 : ℝ) ^ N * x)) atTop (nhds 0) := by
    intro x hx
    let cutoff : ℕ → ℝ := fun N => (2 : ℝ) ^ N * x
    let sets : ℕ → Set ℝ := fun N => {y : ℝ | cutoff N < |y|}
    have hcutoffTop : Tendsto cutoff atTop atTop := by
      simpa [cutoff, mul_comm] using
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop hx
    have hsetsAnti : Antitone sets := by
      intro n m hnm y hy
      have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ m :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hnm
      have hcutoff : cutoff n ≤ cutoff m :=
        mul_le_mul_of_nonneg_right hpow hx.le
      exact lt_of_le_of_lt hcutoff hy
    have hsetsMeas : ∀ N, NullMeasurableSet (sets N) μ := by
      intro N
      exact (measurableSet_lt measurable_const continuous_abs.measurable).nullMeasurableSet
    have hinter : (⋂ N, sets N) = ∅ := by
      ext y
      simp only [Set.mem_iInter, sets, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hy
      obtain ⟨N, hN⟩ :=
        (hcutoffTop.eventually (eventually_gt_atTop |y|)).exists
      exact (lt_asymm hN (hy N))
    have hmeasure := tendsto_measure_iInter_atTop hsetsMeas hsetsAnti
      ⟨0, measure_ne_top μ _⟩
    have hmeasureZero : Tendsto (fun N : ℕ => μ (sets N)) atTop (nhds 0) := by
      change Tendsto (fun N : ℕ => μ (sets N)) atTop
        (nhds (μ (⋂ N, sets N))) at hmeasure
      simpa [hinter] using hmeasure
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmeasureZero
    change Tendsto (fun N : ℕ => (μ (sets N)).toReal) atTop (nhds 0) at hreal
    simpa [tail, cutoff, sets, MeasureTheory.measureReal_def] using hreal

  have hratioLeTsum : ∀ᶠ x : ℝ in atTop,
      0 ≤ x ^ 2 * tail x / V x ∧ x ^ 2 * tail x / V x ≤ ∑' k : ℕ, term x k := by
    filter_upwards [hVpos, eventually_ge_atTop R, eventually_gt_atTop (0 : ℝ),
        htermBound] with x hVx hxR hx htermsBound
    have htermSummable : Summable (term x) :=
      hgeometric.of_norm_bounded htermsBound
    have htailFinite : Tendsto (fun N : ℕ => tail ((2 : ℝ) ^ N * x)) atTop (nhds 0) :=
      htailToZero x hx
    have htelescoping (N : ℕ) : tail x - tail ((2 : ℝ) ^ N * x) =
        ∑ k ∈ Finset.range N,
          (tail ((2 : ℝ) ^ k * x) - tail ((2 : ℝ) ^ (k + 1) * x)) := by
      have h := Finset.sum_range_sub
        (fun k : ℕ => -tail ((2 : ℝ) ^ k * x)) N
      have h' : -tail ((2 : ℝ) ^ N * x) - (-tail x) =
          ∑ k ∈ Finset.range N,
            ((-tail ((2 : ℝ) ^ (k + 1) * x)) -
              (-tail ((2 : ℝ) ^ k * x))) := by
        simpa only [pow_zero, one_mul] using h.symm
      calc
        _ = -tail ((2 : ℝ) ^ N * x) - (-tail x) := by ring
        _ = ∑ k ∈ Finset.range N,
            ((-tail ((2 : ℝ) ^ (k + 1) * x)) -
              (-tail ((2 : ℝ) ^ k * x))) := h'
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
    have hstep : ∀ k : ℕ,
        x ^ 2 * (tail ((2 : ℝ) ^ k * x) - tail ((2 : ℝ) ^ (k + 1) * x)) / V x ≤
          term x k := by
      intro k
      let a : ℝ := (2 : ℝ) ^ k * x
      let b : ℝ := (2 : ℝ) ^ (k + 1) * x
      have ha : 0 ≤ a := by dsimp [a]; positivity
      have hab : a ≤ b := by
        dsimp [a, b]
        have hk : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) := by
          rw [pow_succ]
          nlinarith [sq_nonneg ((2 : ℝ) ^ k - 1)]
        exact mul_le_mul_of_nonneg_right hk hx.le
      have hband := twoSidedTail_difference_mul_sq_le_truncatedSecondMoment_difference
        μ ha hab
      have hpowSq : a ^ 2 = (4 : ℝ) ^ k * x ^ 2 := by
        dsimp [a]
        rw [mul_pow]
        have hpow : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
          calc
            ((2 : ℝ) ^ k) ^ 2 = (2 : ℝ) ^ (k * 2) := by rw [← pow_mul]
            _ = (2 : ℝ) ^ (2 * k) := by congr 1; omega
            _ = ((2 : ℝ) ^ 2) ^ k := by rw [pow_mul]
            _ = (4 : ℝ) ^ k := by norm_num
        rw [hpow]
      have hnum : (4 : ℝ) ^ k * x ^ 2 *
          (tail a - tail b) ≤ V b - V a := by
        simpa [hpowSq, a, b, V] using hband
      have hden : 0 < V x * (4 : ℝ) ^ k := mul_pos hVx (pow_pos (by norm_num) _)
      have hratioEq : term x k = (V b - V a) / (V x * (4 : ℝ) ^ k) := by
        dsimp [term, a, b]
        field_simp [hVx.ne', pow_ne_zero k (by norm_num : (4 : ℝ) ≠ 0)]
      have hleftEq : x ^ 2 * (tail a - tail b) / V x =
          ((4 : ℝ) ^ k * x ^ 2 * (tail a - tail b)) / (V x * (4 : ℝ) ^ k) := by
        field_simp [hVx.ne', pow_ne_zero k (by norm_num : (4 : ℝ) ≠ 0)]
      rw [hleftEq, hratioEq]
      exact div_le_div_of_nonneg_right hnum hden.le
    have hfinite (N : ℕ) : x ^ 2 * tail x / V x ≤
        (∑ k ∈ Finset.range N, term x k) +
          x ^ 2 / V x * tail ((2 : ℝ) ^ N * x) := by
      have hsplit : tail x =
          (∑ k ∈ Finset.range N,
            (tail ((2 : ℝ) ^ k * x) - tail ((2 : ℝ) ^ (k + 1) * x))) +
            tail ((2 : ℝ) ^ N * x) := by
        linarith [htelescoping N]
      have hsumStep : x ^ 2 / V x *
          ∑ k ∈ Finset.range N,
            (tail ((2 : ℝ) ^ k * x) - tail ((2 : ℝ) ^ (k + 1) * x)) ≤
          ∑ k ∈ Finset.range N, term x k := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun k hk => by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hstep k
      calc
        x ^ 2 * tail x / V x = x ^ 2 / V x * tail x := by ring
        _ = x ^ 2 / V x *
            ((∑ k ∈ Finset.range N,
              (tail ((2 : ℝ) ^ k * x) - tail ((2 : ℝ) ^ (k + 1) * x))) +
              tail ((2 : ℝ) ^ N * x)) := by rw [hsplit]
        _ = x ^ 2 / V x *
              ∑ k ∈ Finset.range N,
                (tail ((2 : ℝ) ^ k * x) - tail ((2 : ℝ) ^ (k + 1) * x)) +
            x ^ 2 / V x * tail ((2 : ℝ) ^ N * x) := by ring
        _ ≤ _ := by nlinarith [hsumStep]
    have hsumLimit : Tendsto
        (fun N : ℕ => ∑ k ∈ Finset.range N, term x k) atTop
        (nhds (∑' k : ℕ, term x k)) := htermSummable.hasSum.tendsto_sum_nat
    have hremLimit : Tendsto
        (fun N : ℕ => x ^ 2 / V x * tail ((2 : ℝ) ^ N * x)) atTop (nhds 0) := by
      simpa using htailFinite.const_mul (x ^ 2 / V x)
    have hsumRem := hsumLimit.add hremLimit
    have hle := ge_of_tendsto' hsumRem hfinite
    have hqnonneg : 0 ≤ x ^ 2 * tail x / V x := by
      apply div_nonneg
      · exact mul_nonneg (sq_nonneg x) measureReal_nonneg
      · exact le_of_lt hVx
    exact ⟨hqnonneg, by simpa using hle⟩
  have hlim := tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum
    (hratioLeTsum.mono fun x hx => hx.1)
    (hratioLeTsum.mono fun x hx => hx.2)
  simpa [tail, V] using hlim

end ProbabilityTheory

end

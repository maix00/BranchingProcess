/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Probability.Distributions.CharacteristicFunction.CosineDefect
public import Probability.Distributions.Moments.Truncated
public import Probability.Distributions.Moments.Truncated.RegularVariation

/-!
# Cosine defects and truncated moments

This file records elementary comparisons between a cosine defect and a
truncated second moment. The comparisons are deterministic measure-theoretic
inputs for the exponent-two Gaussian domain-of-attraction endpoint.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- A local fourth-order lower bound for the cosine defect. It follows from
Mathlib's cubic lower bound for sine and is useful when sharpening a quadratic
truncation estimate near the origin. -/
theorem one_sub_cos_lower_bound_quartic {z : ℝ} (hz : |z| ≤ 1) :
    z ^ 2 / 2 - z ^ 4 / 24 ≤ 1 - Real.cos z := by
  let w : ℝ := |z|
  let u : ℝ := w / 2
  have hw : 0 ≤ w := abs_nonneg z
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu_le : u ≤ 1 / 2 := by
    dsimp [u, w]
    nlinarith [abs_nonneg z]
  have hsmall : u ^ 2 ≤ 6 := by nlinarith
  have hq : 0 ≤ u - u ^ 3 / 6 := by nlinarith
  have hsin : u - u ^ 3 / 6 ≤ Real.sin u := Real.sin_ge_sub_cube hu
  have hsin_nonneg : 0 ≤ Real.sin u := hq.trans hsin
  have hsq : (u - u ^ 3 / 6) ^ 2 ≤ Real.sin u ^ 2 :=
    (sq_le_sq₀ hq hsin_nonneg).2 hsin
  have hpoly : w ^ 2 / 2 - w ^ 4 / 24 ≤
      2 * (u - u ^ 3 / 6) ^ 2 := by
    dsimp [u, w]
    nlinarith [sq_nonneg (|z| ^ 3)]
  have hid := Real.sin_sq_eq_half_sub u
  have hcos : 2 * Real.sin u ^ 2 = 1 - Real.cos z := by
    have hdouble : 2 * u = |z| := by dsimp [u, w]; ring
    rw [hid, hdouble, Real.cos_abs]
    ring
  have habs2 : w ^ 2 = z ^ 2 := by dsimp [w]; exact sq_abs z
  have habs4 : w ^ 4 = z ^ 4 := by
    rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, habs2]
    ring
  calc
    z ^ 2 / 2 - z ^ 4 / 24 = w ^ 2 / 2 - w ^ 4 / 24 := by rw [habs2, habs4]
    _ ≤ 2 * (u - u ^ 3 / 6) ^ 2 := hpoly
    _ ≤ 2 * Real.sin u ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 1 - Real.cos z := hcos

/-- A cosine defect controls the truncated second moment on any interval
where the scaled argument stays within one period of the quadratic cosine
bound. -/
theorem cosineDefectIntegral_lower_bound_truncatedSecondMoment
    (μ : Measure ℝ) [IsFiniteMeasure μ] {x : ℝ} (hx : 0 < x) :
    (2 / Real.pi ^ 2) *
        (truncatedSecondMoment μ x / x ^ 2) ≤
      cosineDefectIntegral μ x⁻¹ := by
  let s : Set ℝ := Set.Icc (-x) x
  let c : ℝ := 2 / Real.pi ^ 2
  let f : ℝ → ℝ := fun y => 1 - Real.cos (x⁻¹ * y)
  let g : ℝ → ℝ := s.indicator (fun y => c * (y / x) ^ 2)
  have hs : MeasurableSet s := measurableSet_Icc
  have hc : 0 < c := by dsimp [c]; positivity
  have hf : Integrable f μ := by
    refine Integrable.of_bound (by fun_prop) 2 (ae_of_all _ fun y => ?_)
    dsimp [f]
    rw [abs_le]
    constructor <;> have hcos := Real.neg_one_le_cos (x⁻¹ * y) <;>
      have hcos' := Real.cos_le_one (x⁻¹ * y) <;> linarith
  have hg : Integrable g μ := by
    refine Integrable.of_bound (by fun_prop) c (ae_of_all _ fun y => ?_)
    dsimp [g]
    by_cases hy : y ∈ s
    · rw [Set.indicator_of_mem hy,
        abs_of_nonneg (mul_nonneg hc.le (sq_nonneg _))]
      have hyabs : |y| ≤ x := abs_le.mpr (by simpa [s] using hy)
      have hdiv : |y / x| ≤ 1 := by
        rw [abs_div, abs_of_pos hx]
        exact (div_le_one hx).2 hyabs
      have hsq' : |y / x| ^ 2 ≤ 1 ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hdiv
      have hsq'' : |y / x| ^ 2 ≤ 1 := by nlinarith
      have hsq : (y / x) ^ 2 ≤ 1 := by simpa only [sq_abs] using hsq''
      simpa using (mul_le_mul_of_nonneg_left hsq hc.le)
    · rw [Set.indicator_of_notMem hy]
      simp only [abs_zero]
      exact hc.le
  have hfg : ∀ y, g y ≤ f y := by
    intro y
    by_cases hy : y ∈ s
    · have hyabs : |y| ≤ x := abs_le.mpr (by simpa [s] using hy)
      have hdiv : |y / x| ≤ 1 := by
        rw [abs_div, abs_of_pos hx]
        exact (div_le_one hx).2 hyabs
      have hπ : |y / x| ≤ Real.pi := by
        exact hdiv.trans (by linarith [Real.two_le_pi])
      have hcos := Real.cos_le_one_sub_mul_cos_sq hπ
      change s.indicator (fun z => c * (z / x) ^ 2) y ≤ f y
      rw [Set.indicator_of_mem hy]
      change c * (y / x) ^ 2 ≤ 1 - Real.cos (x⁻¹ * y)
      have hmul : (x⁻¹ * y) = y / x := by
        ring
      rw [hmul]
      dsimp [c]
      linarith
    · change s.indicator (fun z => c * (z / x) ^ 2) y ≤ f y
      rw [Set.indicator_of_notMem hy]
      dsimp [f]
      linarith [Real.cos_le_one (x⁻¹ * y)]
  have hmono := integral_mono_ae hg hf (ae_of_all _ hfg)
  have hgEq : (∫ y, g y ∂μ) = c * (truncatedSecondMoment μ x / x ^ 2) := by
    rw [show g = s.indicator (fun y => c * (y / x) ^ 2) by rfl,
      integral_indicator hs]
    change (∫ y, c * (y / x) ^ 2 ∂(μ.restrict s)) = _
    rw [integral_const_mul]
    have hfun : (fun y : ℝ => (y / x) ^ 2) =
        fun y => x⁻¹ ^ 2 * y ^ 2 := by
      funext y
      rw [div_pow]
      ring
    rw [hfun, integral_const_mul]
    change c * (x⁻¹ ^ 2 * (∫ y in Set.Icc (-x) x, y ^ 2 ∂μ)) =
      c * (truncatedSecondMoment μ x / x ^ 2)
    rw [show (∫ y in Set.Icc (-x) x, y ^ 2 ∂μ) = truncatedSecondMoment μ x by rfl]
    rw [div_eq_mul_inv]
    ring
  rw [cosineDefectIntegral, ← hgEq]
  exact hmono

/-- A sharper lower comparison on a fixed fraction of the truncation window.
The coefficient tends to `1/2` as `δ → 0`; this is the local input needed
to identify the asymptotic ratio under slow variation. -/
theorem cosineDefectIntegral_lower_bound_truncatedSecondMoment_scaled
    (μ : Measure ℝ) [IsFiniteMeasure μ] {x δ : ℝ}
    (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 / 2 - δ ^ 2 / 24) *
        (truncatedSecondMoment μ (δ * x) / x ^ 2) ≤
      cosineDefectIntegral μ x⁻¹ := by
  let cutoff : ℝ := δ * x
  let coeff : ℝ := 1 / 2 - δ ^ 2 / 24
  let s : Set ℝ := Set.Icc (-cutoff) cutoff
  let f : ℝ → ℝ := fun y => 1 - Real.cos (x⁻¹ * y)
  let g : ℝ → ℝ := s.indicator (fun y => coeff * (y / x) ^ 2)
  have hcutoff : 0 < cutoff := by dsimp [cutoff]; positivity
  have hδsq : δ ^ 2 ≤ 1 := by
    have h := (sq_le_sq₀ (abs_nonneg δ) (by norm_num : (0 : ℝ) ≤ 1)).2
      (by simpa [abs_of_pos hδ] using hδ1)
    simpa using h
  have hcoeff : 0 ≤ coeff := by
    dsimp [coeff]
    nlinarith [hδsq]
  have hs : MeasurableSet s := measurableSet_Icc
  have hf : Integrable f μ := by
    refine Integrable.of_bound (by fun_prop) 2 (ae_of_all _ fun y => ?_)
    dsimp [f]
    rw [abs_le]
    constructor <;> have hcos := Real.neg_one_le_cos (x⁻¹ * y) <;>
      have hcos' := Real.cos_le_one (x⁻¹ * y) <;> linarith
  have hg : Integrable g μ := by
    refine Integrable.of_bound (by fun_prop) (coeff * δ ^ 2)
      (ae_of_all _ fun y => ?_)
    dsimp [g]
    by_cases hy : y ∈ s
    · rw [Set.indicator_of_mem hy]
      rw [abs_of_nonneg (mul_nonneg hcoeff (sq_nonneg _))]
      have hyabs : |y| ≤ cutoff := abs_le.mpr (by simpa [s] using hy)
      have hdiv : |y / x| ≤ δ := by
        rw [abs_div, abs_of_pos hx]
        exact (div_le_iff₀ hx).2 (by simpa [cutoff] using hyabs)
      have hdivsqAbs : |y / x| ^ 2 ≤ δ ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (le_of_lt hδ)).2 hdiv
      have hdivsq : (y / x) ^ 2 ≤ δ ^ 2 := by
        simpa only [sq_abs] using hdivsqAbs
      exact mul_le_mul_of_nonneg_left hdivsq hcoeff
    · rw [Set.indicator_of_notMem hy]
      simp only [abs_zero]
      exact mul_nonneg hcoeff (sq_nonneg _)
  have hfg : ∀ y, g y ≤ f y := by
    intro y
    by_cases hy : y ∈ s
    · have hyabs : |y| ≤ cutoff := abs_le.mpr (by simpa [s] using hy)
      have hdiv : |y / x| ≤ δ := by
        rw [abs_div, abs_of_pos hx]
        exact (div_le_iff₀ hx).2 (by simpa [cutoff] using hyabs)
      have hdivleone : |y / x| ≤ 1 := hdiv.trans hδ1
      have hquartic := one_sub_cos_lower_bound_quartic hdivleone
      have hdivsqAbs : |y / x| ^ 2 ≤ δ ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (le_of_lt hδ)).2 hdiv
      have hdivsq : (y / x) ^ 2 ≤ δ ^ 2 := by
        simpa only [sq_abs] using hdivsqAbs
      have hfour : (y / x) ^ 4 ≤ δ ^ 2 * (y / x) ^ 2 := by
        calc
          (y / x) ^ 4 = (y / x) ^ 2 * (y / x) ^ 2 := by ring
          _ ≤ δ ^ 2 * (y / x) ^ 2 :=
            mul_le_mul_of_nonneg_right hdivsq (sq_nonneg _)
      change s.indicator (fun z => coeff * (z / x) ^ 2) y ≤
        1 - Real.cos (x⁻¹ * y)
      rw [Set.indicator_of_mem hy]
      have hmul : x⁻¹ * y = y / x := by ring
      rw [hmul]
      dsimp [coeff] at hquartic ⊢
      nlinarith [hquartic, hfour]
    · change s.indicator (fun z => coeff * (z / x) ^ 2) y ≤
        1 - Real.cos (x⁻¹ * y)
      rw [Set.indicator_of_notMem hy]
      linarith [Real.cos_le_one (x⁻¹ * y)]
  have hmono := integral_mono_ae hg hf (ae_of_all _ hfg)
  have hgEq : (∫ y, g y ∂μ) =
      coeff * (truncatedSecondMoment μ cutoff / x ^ 2) := by
    rw [show g = s.indicator (fun y => coeff * (y / x) ^ 2) by rfl,
      integral_indicator hs]
    change (∫ y, coeff * (y / x) ^ 2 ∂(μ.restrict s)) = _
    have hfun : (fun y : ℝ => coeff * (y / x) ^ 2) =
        fun y => (coeff * x⁻¹ ^ 2) * y ^ 2 := by
      funext y
      rw [div_pow]
      ring
    rw [hfun, integral_const_mul]
    change (coeff * x⁻¹ ^ 2) *
        (∫ y in Set.Icc (-cutoff) cutoff, y ^ 2 ∂μ) = _
    rw [show (∫ y in Set.Icc (-cutoff) cutoff, y ^ 2 ∂μ) =
        truncatedSecondMoment μ cutoff by rfl]
    dsimp [cutoff]
    field_simp [ne_of_gt hx]
  rw [cosineDefectIntegral, ← hgEq]
  simpa [coeff, cutoff] using hmono

/-- A cosine defect is bounded above by the truncated quadratic contribution
plus twice the probability outside the truncation interval. -/
theorem cosineDefectIntegral_upper_bound_truncatedSecondMoment_add_tail
    (μ : Measure ℝ) [IsFiniteMeasure μ] {x : ℝ} (hx : 0 < x) :
    cosineDefectIntegral μ x⁻¹ ≤
      truncatedSecondMoment μ x / (2 * x ^ 2) +
        2 * μ.real {y : ℝ | x < |y|} := by
  let s : Set ℝ := Set.Icc (-x) x
  let f : ℝ → ℝ := fun y => 1 - Real.cos (x⁻¹ * y)
  let g : ℝ → ℝ :=
    s.indicator (fun y => (y / x) ^ 2 / 2) +
      sᶜ.indicator (fun _ : ℝ => 2)
  have hs : MeasurableSet s := measurableSet_Icc
  have hq : Measurable (fun y : ℝ => (y / x) ^ 2 / 2) := by fun_prop
  have htwo : Measurable (fun _ : ℝ => (2 : ℝ)) := measurable_const
  have hgMeas : Measurable g := by
    dsimp [g]
    exact (Measurable.indicator hq hs).add
      (Measurable.indicator htwo hs.compl)
  have hf : Integrable f μ := by
    refine Integrable.of_bound (by fun_prop) 2
      (ae_of_all _ fun y => ?_)
    dsimp [f]
    rw [abs_le]
    constructor <;> have hcos := Real.neg_one_le_cos (x⁻¹ * y) <;>
      have hcos' := Real.cos_le_one (x⁻¹ * y) <;> linarith
  have hg : Integrable g μ := by
    refine Integrable.of_bound hgMeas.aestronglyMeasurable 2
      (ae_of_all _ fun y => ?_)
    dsimp [g]
    by_cases hy : y ∈ s
    · rw [Set.indicator_of_mem hy, Set.indicator_of_notMem (by simpa using hy)]
      simp only [add_zero]
      have hyabs : |y| ≤ x := abs_le.mpr (by simpa [s] using hy)
      have hdiv : |y / x| ≤ 1 := by
        rw [abs_div, abs_of_pos hx]
        exact (div_le_one hx).2 hyabs
      rw [abs_of_nonneg (by positivity : 0 ≤ (y / x) ^ 2 / 2)]
      have hsq : (y / x) ^ 2 ≤ 1 := by
        have habsSq : |y / x| ^ 2 ≤ 1 ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hdiv
        have habsSq' : |y / x| ^ 2 ≤ 1 := by nlinarith
        simpa only [sq_abs] using habsSq'
      nlinarith
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_mem (by simpa using hy)]
      norm_num
  have hfg : ∀ y, f y ≤ g y := by
    intro y
    by_cases hy : y ∈ s
    · change f y ≤
        s.indicator (fun z => (z / x) ^ 2 / 2) y +
          sᶜ.indicator (fun _ : ℝ => 2) y
      rw [Set.indicator_of_mem hy, Set.indicator_of_notMem (by simpa using hy)]
      have hmul : x⁻¹ * y = y / x := by ring
      dsimp [f]
      rw [hmul]
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := y / x)]
    · change f y ≤
        s.indicator (fun z => (z / x) ^ 2 / 2) y +
          sᶜ.indicator (fun _ : ℝ => 2) y
      rw [Set.indicator_of_notMem hy, Set.indicator_of_mem (by simpa using hy)]
      dsimp [f]
      linarith [Real.neg_one_le_cos (x⁻¹ * y)]
  have hleft : Integrable (s.indicator (fun y : ℝ => (y / x) ^ 2 / 2)) μ := by
    refine Integrable.of_bound (Measurable.indicator hq hs).aestronglyMeasurable 2
      (ae_of_all _ fun y => ?_)
    by_cases hy : y ∈ s
    · rw [Set.indicator_of_mem hy, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      have hyabs : |y| ≤ x := abs_le.mpr (by simpa [s] using hy)
      have hdiv : |y / x| ≤ 1 := by
        rw [abs_div, abs_of_pos hx]
        exact (div_le_one hx).2 hyabs
      have hsq : (y / x) ^ 2 ≤ 1 := by
        have habsSq : |y / x| ^ 2 ≤ 1 ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hdiv
        have habsSq' : |y / x| ^ 2 ≤ 1 := by nlinarith
        simpa only [sq_abs] using habsSq'
      nlinarith
    · rw [Set.indicator_of_notMem hy]
      simp
  have hright : Integrable (sᶜ.indicator (fun _ : ℝ => (2 : ℝ))) μ := by
    refine Integrable.of_bound (Measurable.indicator htwo hs.compl).aestronglyMeasurable 2
      (ae_of_all _ fun y => ?_)
    by_cases hy : y ∈ sᶜ
    · rw [Set.indicator_of_mem hy]
      simp
    · rw [Set.indicator_of_notMem hy]
      simp
  have hmono := integral_mono_ae hf hg (ae_of_all _ hfg)
  have hgEq : (∫ y, g y ∂μ) =
      truncatedSecondMoment μ x / (2 * x ^ 2) +
        2 * μ.real {y : ℝ | x < |y|} := by
    change (∫ y, s.indicator (fun y : ℝ => (y / x) ^ 2 / 2) y +
        sᶜ.indicator (fun _ : ℝ => (2 : ℝ)) y ∂μ) = _
    rw [integral_add hleft hright, integral_indicator hs, integral_indicator hs.compl]
    have hinner : (∫ y in s, (y / x) ^ 2 / 2 ∂μ) =
        truncatedSecondMoment μ x / (2 * x ^ 2) := by
      have hfun : (fun y : ℝ => (y / x) ^ 2 / 2) =
          fun y => (x⁻¹ ^ 2 / 2) * y ^ 2 := by
        funext y
        rw [div_pow]
        ring
      rw [hfun, integral_const_mul]
      change x⁻¹ ^ 2 / 2 * truncatedSecondMoment μ x = _
      rw [div_eq_mul_inv]
      field_simp [hx.ne']
    have hsComplement : sᶜ = {y : ℝ | x < |y|} := by
      ext y
      change ¬ (-x ≤ y ∧ y ≤ x) ↔ x < |y|
      constructor
      · intro hy
        by_contra h
        exact hy (abs_le.mp (le_of_not_gt h))
      · intro hy h
        exact (not_lt_of_ge (abs_le.mpr h)) hy
    rw [hinner, hsComplement, setIntegral_const, smul_eq_mul]
    ring
  rw [cosineDefectIntegral, ← hgEq]
  exact hmono

/-- If the truncated second moment is slowly varying and the quadratic tail
is negligible, then the cosine defect has the expected quadratic asymptotic.
This is a measure-level comparison theorem; it makes no centering assumption. -/
theorem tendsto_normalizedCosineDefect_of_slowVariation_and_tail
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hVslow : Asymptotics.IsSlowlyVaryingAtTop (truncatedSecondMoment μ))
    (hTail : Tendsto
      (fun x : ℝ => x ^ 2 * μ.real {y : ℝ | x < |y|} /
        truncatedSecondMoment μ x) atTop (nhds 0)) :
    Tendsto
      (fun x : ℝ => 2 * x ^ 2 * cosineDefectIntegral μ x⁻¹ /
        truncatedSecondMoment μ x)
      atTop (nhds 1) := by
  let V : ℝ → ℝ := truncatedSecondMoment μ
  let tail : ℝ → ℝ := fun x => μ.real {y : ℝ | x < |y|}
  let ratio : ℝ → ℝ := fun x => 2 * x ^ 2 * cosineDefectIntegral μ x⁻¹ / V x
  have hVpos : ∀ᶠ x : ℝ in atTop, 0 < V x := hVslow.eventually_pos
  have hTail' : Tendsto (fun x : ℝ => x ^ 2 * tail x / V x) atTop (nhds 0) := by
    simpa [V, tail] using hTail
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    let ε : ℝ := 1 - b
    have hε : 0 < ε := by dsimp [ε]; linarith
    let δ : ℝ := min 1 (Real.sqrt ε)
    have hδ : 0 < δ := lt_min zero_lt_one (Real.sqrt_pos.2 hε)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδsqrt : δ ≤ Real.sqrt ε := min_le_right _ _
    have hδsq : δ ^ 2 ≤ ε := by
      have hsq := (sq_le_sq₀ hδ.le (Real.sqrt_nonneg ε)).2 hδsqrt
      simpa [Real.sq_sqrt hε.le] using hsq
    have herror : δ ^ 2 / 12 < ε := by nlinarith [hδsq]
    let a : ℝ := 1 - δ ^ 2 / 12
    have hba : b < a := by dsimp [a, ε]; linarith
    have hVscale : Tendsto (fun x : ℝ => V (δ * x) / V x) atTop (nhds 1) := by
      simpa [V, Real.rpow_zero] using hVslow.ratio_tendsto hδ
    have hscaledLower : Tendsto
        (fun x : ℝ => a * (V (δ * x) / V x)) atTop (nhds a) := by
      simpa [a] using hVscale.const_mul a
    have hlowerEvent : ∀ᶠ x : ℝ in atTop, b < a * (V (δ * x) / V x) :=
      hscaledLower.eventually (Ioi_mem_nhds hba)
    have hratioLower : ∀ᶠ x : ℝ in atTop,
        a * (V (δ * x) / V x) ≤ ratio x := by
      filter_upwards [hVpos, eventually_gt_atTop (0 : ℝ)] with x hVx hx
      have hlocal := cosineDefectIntegral_lower_bound_truncatedSecondMoment_scaled
        μ hx hδ hδ1
      have hfactor : 0 ≤ 2 * x ^ 2 / V x := by positivity
      have hmul := mul_le_mul_of_nonneg_left hlocal hfactor
      have hcoeff :
          2 * x ^ 2 / V x *
              ((1 / 2 - δ ^ 2 / 24) * (V (δ * x) / x ^ 2)) =
            a * (V (δ * x) / V x) := by
        dsimp [a]
        field_simp [ne_of_gt hx, ne_of_gt hVx]
        ring
      calc
        a * (V (δ * x) / V x) =
            2 * x ^ 2 / V x *
              ((1 / 2 - δ ^ 2 / 24) * (V (δ * x) / x ^ 2)) := hcoeff.symm
        _ ≤ 2 * x ^ 2 / V x * cosineDefectIntegral μ x⁻¹ := hmul
        _ = ratio x := by
          dsimp [ratio]
          field_simp [ne_of_gt hVx]
    filter_upwards [hlowerEvent, hratioLower] with x h₁ h₂
    exact h₁.trans_le h₂
  · intro b hb
    let ε : ℝ := (b - 1) / 4
    have hε : 0 < ε := by dsimp [ε]; linarith
    have htailSmall : ∀ᶠ x : ℝ in atTop, x ^ 2 * tail x / V x < ε :=
      hTail'.eventually (Iio_mem_nhds hε)
    have hratioUpper : ∀ᶠ x : ℝ in atTop,
        ratio x ≤ 1 + 4 * (x ^ 2 * tail x / V x) := by
      filter_upwards [hVpos, eventually_gt_atTop (0 : ℝ)] with x hVx hx
      have hlocal := cosineDefectIntegral_upper_bound_truncatedSecondMoment_add_tail
        μ hx
      have hfactor : 0 ≤ 2 * x ^ 2 / V x := by positivity
      have hmul := mul_le_mul_of_nonneg_left hlocal hfactor
      have hcoeff :
          2 * x ^ 2 / V x *
              (V x / (2 * x ^ 2) + 2 * tail x) =
            1 + 4 * (x ^ 2 * tail x / V x) := by
        field_simp [ne_of_gt hx, ne_of_gt hVx]
        ring
      calc
        ratio x = 2 * x ^ 2 / V x * cosineDefectIntegral μ x⁻¹ := by
          dsimp [ratio]
          field_simp [ne_of_gt hVx]
        _ ≤ 2 * x ^ 2 / V x *
            (V x / (2 * x ^ 2) + 2 * tail x) := hmul
        _ = 1 + 4 * (x ^ 2 * tail x / V x) := hcoeff
    filter_upwards [htailSmall, hratioUpper] with x htail hratio
    dsimp [ε] at htail
    linarith

/-- The normalized cosine defect is asymptotic to the truncated second
moment whenever that moment is slowly varying. The quadratic-tail condition
needed by the comparison is supplied by the Feller criterion for truncated
second moments. -/
theorem tendsto_normalizedCosineDefect_of_slowVariation
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hVslow : Asymptotics.IsSlowlyVaryingAtTop (truncatedSecondMoment μ)) :
    Tendsto
      (fun x : ℝ => 2 * x ^ 2 * cosineDefectIntegral μ x⁻¹ /
        truncatedSecondMoment μ x)
      atTop (nhds 1) :=
  tendsto_normalizedCosineDefect_of_slowVariation_and_tail μ hVslow
    (tendsto_secondTailRatio_of_slowlyVarying_truncatedSecondMoment μ hVslow)

end ProbabilityTheory

end

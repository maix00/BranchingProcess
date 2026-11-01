/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Semigroup.Basic
import MeasureTheory.Measure.Levy.JumpRegions
import Probability.Distributions.CharacteristicFunction.CosineDefect
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Scaled jump-mass bounds in the Lévy–Khintchine proof

## Internal proof declarations

* `scaled_mass_bound_real ε hε` bounds `t⁻¹ μ_t({x | ε ≤ |x|})` uniformly for `t > 0`.
* `scaled_mass_bound_real_with_max` and `scaled_largeJumpSet_mass_le_of_large_radius` choose a
  tail radius from continuity of the exponent. These are proof inputs to canonical-measure
  extraction, rather than separate probability APIs.

For each $\varepsilon>0$, the scaled mass outside $[-\varepsilon,\varepsilon]$
is uniformly bounded for small $t$:
\[
  \sup_{0<t<t_0(\varepsilon)}\frac1t
       \mu_t\{x:\varepsilon\le|x|\}<\infty.
\]
-/

section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder

namespace ProbabilityTheory

namespace ConvolutionSemigroup

variable (S : ConvolutionSemigroup)

/-! ### 3.1 — Uniform boundedness of scaled measures on large sets -/

/-- The integral of `1 - cos(xξ)` is non-negative. -/
private lemma one_sub_cos_nonneg (ξ : ℝ) (x : ℝ) : 0 ≤ 1 - Real.cos (x * ξ) :=
  sub_nonneg.mpr (Real.cos_le_one _)

/-- `fun x => 1 - cos(x * ξ)` is integrable against a finite measure restricted to any set. -/
private lemma integrableOn_one_sub_cos {μ : Measure ℝ} [IsFiniteMeasure μ] (ξ : ℝ) (s : Set ℝ) :
    IntegrableOn (fun x => 1 - Real.cos (x * ξ)) s μ :=
  Integrable.of_bound
    ((continuous_const.sub
      (Real.continuous_cos.comp (continuous_id'.mul continuous_const))).aestronglyMeasurable)
    2 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (one_sub_cos_nonneg ξ x)]
      linarith [Real.neg_one_le_cos (x * ξ)])


/-- **Real-valued scaled mass bound.** The quantity `t⁻¹ · μ_t({|x| ≥ ε})` is
    uniformly bounded over all `t > 0`.

    **Proof sketch:**
    1. For `|x| ≥ ε`: `∫₀^{2/ε} (1-cos(xξ)) dξ = 2/ε - sin(2x/ε)/x ≥ 1/ε`.
    2. By Fubini: `ε⁻¹ · μ({|x| ≥ ε}) ≤ ∫₀^{2/ε} (1 - Re(charFun μ ξ)) dξ`.
    3. Using `charFun(μ_t)(ξ) = exp(tψ(ξ))` and the bound
       `t⁻¹(1-Re(exp(tψ))) ≤ 2‖ψ‖` (from `‖exp z - 1‖ ≤ 2‖z‖` for `‖z‖ ≤ 1`
       and `1-Re(exp(tψ)) ≤ 2` with `t⁻¹ ≤ ‖ψ‖` otherwise):
       `t⁻¹ · μ_t({|x| ≥ ε}) ≤ 4 · sup_{ξ ∈ [0,2/ε]} ‖ψ(ξ)‖`. -/
lemma scaled_mass_bound_real (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ (t : {t : ℝ // 0 < t}),
      t.val⁻¹ * ((S.measure t : Measure ℝ) (largeJumpSet ε)).toReal ≤ ↑C := by
  -- The exponent attains a maximum norm M on the compact interval [0, 2/ε].
  obtain ⟨ξ_max, -, hξ_max⟩ := isCompact_Icc.exists_isMaxOn
    (⟨0, Set.left_mem_Icc.mpr (by positivity)⟩ : (Set.Icc (0:ℝ) (2/ε)).Nonempty)
    S.exponent_continuous.norm.continuousOn
  set M := ‖S.exponent ξ_max‖ with hM_def
  -- Key uniform bound: t⁻¹ * Re(1-exp(tψ(ξ))) ≤ 2M for ξ ∈ [0,2/ε], t > 0.
  have hkey : ∀ ξ ∈ Set.Icc (0:ℝ) (2/ε), ∀ (t : {t : ℝ // 0 < t}),
      t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤ 2 * M := by
    intro ξ hξ t
    have hξM : ‖S.exponent ξ‖ ≤ M := hξ_max hξ
    -- ‖exp(tψ(ξ))‖ ≤ 1 via the `charFun` identity
    have hexp_le1 : ‖exp ((t.val : ℂ) * S.exponent ξ)‖ ≤ 1 := by
      let : IsProbabilityMeasure (S.measure t : Measure ℝ) := (S.measure t).prop
      have h := norm_charFun_le_one (μ := (S.measure t : Measure ℝ)) ξ
      rwa [S.charFun_eq t ξ] at h
    -- (1-exp(tψ)).re ≤ 2
    have hre_le2 : (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤ 2 := by
      have hge : -1 ≤ (exp ((t.val : ℂ) * S.exponent ξ)).re := by
        have h1 : |(exp ((t.val : ℂ) * S.exponent ξ)).re| ≤ 1 :=
          (Complex.abs_re_le_norm _).trans hexp_le1
        linarith [neg_abs_le (exp ((t.val : ℂ) * S.exponent ξ)).re]
      simp only [sub_re, one_re]; linarith
    -- Case split on t * ‖ψ(ξ)‖ ≤ 1 vs > 1
    by_cases h : t.val * ‖S.exponent ξ‖ ≤ 1
    · -- Small regime: use norm_exp_sub_one_le
      have htz : ‖(t.val : ℂ) * S.exponent ξ‖ ≤ 1 := by
        simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg t.prop.le]; exact h
      have h_re : (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤ 2 * t.val * ‖S.exponent ξ‖ :=
        calc (1 - exp ((t.val : ℂ) * S.exponent ξ)).re
            ≤ ‖1 - exp ((t.val : ℂ) * S.exponent ξ)‖ := Complex.re_le_norm _
          _ = ‖exp ((t.val : ℂ) * S.exponent ξ) - 1‖ := norm_sub_rev _ _
          _ ≤ 2 * ‖(t.val : ℂ) * S.exponent ξ‖ := Complex.norm_exp_sub_one_le htz
          _ = 2 * t.val * ‖S.exponent ξ‖ := by
                simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg t.prop.le]; ring
      calc t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re
          ≤ t.val⁻¹ * (2 * t.val * ‖S.exponent ξ‖) :=
              mul_le_mul_of_nonneg_left h_re (le_of_lt (inv_pos.mpr t.prop))
        _ = 2 * ‖S.exponent ξ‖ := by field_simp [ne_of_gt t.prop]
        _ ≤ 2 * M := by linarith
    · -- Large regime: t⁻¹ ≤ ‖ψ(ξ)‖, use (1-exp).re ≤ 2
      push Not at h
      have hψ_pos : (0 : ℝ) < ‖S.exponent ξ‖ := by
        rcases ne_or_eq (S.exponent ξ) 0 with hne | h0
        · exact norm_pos_iff.mpr hne
        · simp only [h0, norm_zero] at h; linarith
      have ht_inv : t.val⁻¹ ≤ ‖S.exponent ξ‖ :=
        (inv_le_iff_one_le_mul₀' t.prop).mpr (le_of_lt h)
      calc t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re
          ≤ t.val⁻¹ * 2 :=
              mul_le_mul_of_nonneg_left hre_le2 (le_of_lt (inv_pos.mpr t.prop))
        _ ≤ ‖S.exponent ξ‖ * 2 := by nlinarith
        _ ≤ M * 2 := by nlinarith
        _ = 2 * M := by ring
  -- Use C = 4*M + 1 as the uniform bound
  refine ⟨⟨4 * M + 1, by positivity⟩, fun t => ?_⟩
  set μ := (S.measure t : Measure ℝ)
  have : IsProbabilityMeasure μ := inferInstance
  -- The integrand 1-cos(ξ*x) is nonneg and bounded
  have h_nn : ∀ (ξ x : ℝ), 0 ≤ 1 - Real.cos (ξ * x) := fun ξ x => one_sub_cos_nonneg x ξ
  -- Integrability of (ξ, x) ↦ 1-cos(ξx) on [0,2/ε] × ℝ under volume × μ
  -- The product volume.restrict(uIoc) × μ is finite (μ is a prob measure)
  have hfin_restrict : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) (2/ε))) := by
    rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ 2/ε)]
    infer_instance
  have hfubini_int : Integrable (fun p : ℝ × ℝ => 1 - Real.cos (p.1 * p.2))
      ((volume.restrict (Set.uIoc 0 (2/ε))).prod μ) :=
    Integrable.of_bound
      ((continuous_const.sub (Real.continuous_cos.comp
        (continuous_fst.mul continuous_snd))).aestronglyMeasurable)
      2
      (ae_of_all _ fun p => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (h_nn p.1 p.2)]
        linarith [Real.neg_one_le_cos (p.1 * p.2)])
  -- Fubini: ∫_ξ ∫_x (1-cos) dμ dξ = ∫_x ∫_ξ (1-cos) dξ dμ
  have hfubini : ∫ ξ in (0:ℝ)..(2/ε), ∫ x, (1 - Real.cos (ξ * x)) ∂μ =
      ∫ x, (∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))) ∂μ :=
    intervalIntegral_integral_swap hfubini_int
  -- ∫_ξ ∫_x (1-cos) dμ = ∫_ξ Re(1-exp(tψ)) dξ
  have hrhs : ∫ ξ in (0:ℝ)..(2/ε), ∫ x, (1 - Real.cos (ξ * x)) ∂μ =
      ∫ ξ in (0:ℝ)..(2/ε), (1 - exp ((t.val : ℂ) * S.exponent ξ)).re := by
    congr 1; ext ξ
    change cosineDefectIntegral μ ξ = (1 - exp ((t.val : ℂ) * S.exponent ξ)).re
    rw [cosineDefectIntegral_eq_one_sub_charFun_re μ ξ, S.charFun_eq t ξ]
    simp
  -- Integrability of x ↦ ∫_ξ (1-cos) dξ under μ (bounded by 4/ε via |1-cos| ≤ 2)
  have h_intcont : Continuous (fun x => ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x ξ => 1 - Real.cos (ξ * x))
      (by fun_prop) 0 (2/ε)
  have hint_outer : Integrable (fun x => ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))) μ :=
    Integrable.of_bound
      h_intcont.aestronglyMeasurable
      (4/ε)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg
            (intervalIntegral.integral_nonneg (by positivity) fun ξ _ => h_nn ξ x)]
        have hfx_int : IntervalIntegrable (fun ξ => 1 - Real.cos (ξ * x)) volume 0 (2/ε) :=
          (continuous_const.sub (Real.continuous_cos.comp
            (continuous_id.mul continuous_const))).intervalIntegrable 0 (2/ε)
        calc ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))
            ≤ ∫ ξ in (0:ℝ)..(2/ε), (2 : ℝ) :=
              intervalIntegral.integral_mono_on (by positivity) hfx_int intervalIntegrable_const
                (fun ξ _ => by linarith [Real.neg_one_le_cos (ξ * x)])
          _ = 4/ε := by
              rw [intervalIntegral.integral_const, smul_eq_mul]
              field_simp; ring)
  -- Pointwise bound: ∫_0^{2/ε} (1-cos(ξx)) dξ ≥ ε⁻¹ for x ∈ largeJumpSet ε
  have hpointwise : ∀ x ∈ largeJumpSet ε,
      ε⁻¹ ≤ ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x)) := by
    intro x hx
    have hxε : ε ≤ |x| := mem_largeJumpSet.mp hx
    have hx_ne : x ≠ 0 := by
      intro h0; simp only [h0, abs_zero] at hxε; linarith
    -- The integral of cos(ξx) over ξ ∈ [0, 2/ε]: substitute u = ξ*x
    have hcos_int : IntervalIntegrable (fun ξ => Real.cos (ξ * x)) volume 0 (2/ε) :=
      (Real.continuous_cos.comp (continuous_id.mul continuous_const)).intervalIntegrable 0 (2/ε)
    have hmul : ∫ ξ in (0:ℝ)..(2/ε), Real.cos (ξ * x) = Real.sin (2 * x / ε) / x := by
      rw [intervalIntegral.integral_comp_mul_right (hc := hx_ne)]
      simp only [zero_mul, smul_eq_mul]
      -- integral_cos: ∫ in 0..2/ε*x, cos = sin(2/ε*x) - sin(0)
      rw [integral_cos, Real.sin_zero, sub_zero]
      rw [show (2 : ℝ) / ε * x = 2 * x / ε from by ring]
      rw [div_eq_mul_inv (Real.sin _) x, mul_comm]
    have hcomp : ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x)) =
        2/ε - Real.sin (2 * x / ε) / x := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hcos_int,
        intervalIntegral.integral_const, smul_eq_mul, mul_one, hmul]
      ring
    rw [hcomp]
    have hsin_bd : Real.sin (2 * x / ε) / x ≤ 1/ε := by
      have habs : |Real.sin (2 * x / ε) / x| ≤ 1/ε := by
        rw [abs_div, div_le_div_iff₀ (abs_pos.mpr hx_ne) hε]
        nlinarith [Real.abs_sin_le_one (2 * x / ε)]
      linarith [le_abs_self (Real.sin (2 * x / ε) / x)]
    have h1e : (1:ℝ)/ε = ε⁻¹ := one_div ε
    have h2e : (2:ℝ)/ε = 2 * ε⁻¹ := by rw [div_eq_mul_inv]
    linarith
  -- Main bound: ε⁻¹ * μ(largeJumpSet ε) ≤ ∫_x ∫_ξ (1-cos) dξ dμ = ∫_ξ ∫_x (1-cos) dμ dξ
  have hmass : ε⁻¹ * (μ (largeJumpSet ε)).toReal ≤
      ∫ ξ in (0:ℝ)..(2/ε), (1 - exp ((t.val : ℂ) * S.exponent ξ)).re := by
    rw [← hrhs, hfubini]
    rw [show ε⁻¹ * (μ (largeJumpSet ε)).toReal =
      ∫ _ in largeJumpSet ε, ε⁻¹ ∂μ by
        rw [setIntegral_const, smul_eq_mul, Measure.real_def, mul_comm]]
    exact le_trans
      (setIntegral_mono_on integrableOn_const hint_outer.integrableOn
        (measurableSet_largeJumpSet ε) (fun x hx => hpointwise x hx))
      (setIntegral_le_integral hint_outer (ae_of_all _ (fun x =>
        intervalIntegral.integral_nonneg (by positivity) fun ξ _ => h_nn ξ x)))
  -- Multiply by t⁻¹: t⁻¹ * ε⁻¹ * μ(largeJumpSet ε) ≤ ∫_ξ t⁻¹*(1-exp).re dξ
  have ht_inv_nn : 0 ≤ t.val⁻¹ := le_of_lt (inv_pos.mpr t.prop)
  have hmass_t : t.val⁻¹ * ε⁻¹ * (μ (largeJumpSet ε)).toReal ≤
      ∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re := by
    have hrearrange : t.val⁻¹ * ε⁻¹ * (μ (largeJumpSet ε)).toReal =
        t.val⁻¹ * (ε⁻¹ * (μ (largeJumpSet ε)).toReal) := by ring
    rw [hrearrange]
    calc t.val⁻¹ * (ε⁻¹ * (μ (largeJumpSet ε)).toReal)
        ≤ t.val⁻¹ * (∫ ξ in (0:ℝ)..(2/ε), (1 - exp ((↑t.val : ℂ) * S.exponent ξ)).re) :=
          mul_le_mul_of_nonneg_left hmass ht_inv_nn
      _ = ∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((↑t.val : ℂ) * S.exponent ξ)).re := by
          rw [← intervalIntegral.integral_const_mul]
  -- IntervalIntegrable for the t-scaled exponent integrand
  have hint_exp : IntervalIntegrable
      (fun ξ => t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re) volume 0 (2/ε) :=
    ((continuous_const.sub
        (Complex.continuous_re.comp
          (Complex.continuous_exp.comp
            (continuous_const.mul S.exponent_continuous)))).const_mul _).intervalIntegrable _ _
  -- Bound the integrand by 2M (using hkey)
  have hint_2M : ∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤
      ∫ ξ in (0:ℝ)..(2/ε), (2 * M) :=
    intervalIntegral.integral_mono_on (by positivity) hint_exp intervalIntegrable_const
      (fun ξ hξ => hkey ξ hξ t)
  -- ∫_0^{2/ε} 2M = 4M/ε
  have hint_const : ∫ ξ in (0:ℝ)..(2/ε), (2 * M) = 4 * M / ε := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    field_simp [hε.ne']
    ring
  -- Combine: t⁻¹ * μ(largeJumpSet ε) ≤ 4M ≤ 4M + 1
  calc t.val⁻¹ * (μ (largeJumpSet ε)).toReal
      = ε * (t.val⁻¹ * ε⁻¹ * (μ (largeJumpSet ε)).toReal) := by field_simp [hε.ne', ne_of_gt t.prop]
    _ ≤ ε * (∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((↑t.val : ℂ) * S.exponent ξ)).re) := by
        exact mul_le_mul_of_nonneg_left hmass_t (le_of_lt hε)
    _ ≤ ε * (∫ ξ in (0:ℝ)..(2/ε), (2 * M)) := by
        apply mul_le_mul_of_nonneg_left hint_2M (le_of_lt hε)
    _ = ε * (4 * M / ε) := by rw [hint_const]
    _ = 4 * M := by field_simp [hε.ne']
    _ ≤ 4 * M + 1 := by linarith

/-- **Real-valued mass bound parameterized by the max of `‖ψ‖` on `[0, 2/ε]`.**
    Variant of `scaled_mass_bound_real` that exposes the bound `4·M` explicitly,
    where `M` is the supremum of `‖ψ‖` on `[0, 2/ε]`. This is used for tightness:
    as `ε → ∞`, the interval `[0, 2/ε]` shrinks to `{0}` and `M → 0` since `ψ(0) = 0`.
-/
lemma scaled_mass_bound_real_with_max (ε : ℝ) (hε : 0 < ε)
    (M : ℝ) (_hM_nn : 0 ≤ M)
    (hM : ∀ ξ ∈ Set.Icc (0:ℝ) (2/ε), ‖S.exponent ξ‖ ≤ M) :
    ∀ (t : {t : ℝ // 0 < t}),
      t.val⁻¹ * ((S.measure t : Measure ℝ) (largeJumpSet ε)).toReal ≤ 4 * M := by
  -- Reuses the proof structure of `scaled_mass_bound_real`, replacing the
  -- internally-computed max with the user-supplied bound `M`.
  intro t
  -- Key uniform bound: t⁻¹ * Re(1-exp(tψ(ξ))) ≤ 2M for ξ ∈ [0,2/ε], t > 0.
  have hkey : ∀ ξ ∈ Set.Icc (0:ℝ) (2/ε),
      t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤ 2 * M := by
    intro ξ hξ
    have hξM : ‖S.exponent ξ‖ ≤ M := hM ξ hξ
    have hexp_le1 : ‖exp ((t.val : ℂ) * S.exponent ξ)‖ ≤ 1 := by
      let : IsProbabilityMeasure (S.measure t : Measure ℝ) := (S.measure t).prop
      have h := norm_charFun_le_one (μ := (S.measure t : Measure ℝ)) ξ
      rwa [S.charFun_eq t ξ] at h
    have hre_le2 : (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤ 2 := by
      have hge : -1 ≤ (exp ((t.val : ℂ) * S.exponent ξ)).re := by
        have h1 : |(exp ((t.val : ℂ) * S.exponent ξ)).re| ≤ 1 :=
          (Complex.abs_re_le_norm _).trans hexp_le1
        linarith [neg_abs_le (exp ((t.val : ℂ) * S.exponent ξ)).re]
      simp only [sub_re, one_re]; linarith
    by_cases h : t.val * ‖S.exponent ξ‖ ≤ 1
    · have htz : ‖(t.val : ℂ) * S.exponent ξ‖ ≤ 1 := by
        simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg t.prop.le]; exact h
      have h_re : (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤ 2 * t.val * ‖S.exponent ξ‖ :=
        calc (1 - exp ((t.val : ℂ) * S.exponent ξ)).re
            ≤ ‖1 - exp ((t.val : ℂ) * S.exponent ξ)‖ := Complex.re_le_norm _
          _ = ‖exp ((t.val : ℂ) * S.exponent ξ) - 1‖ := norm_sub_rev _ _
          _ ≤ 2 * ‖(t.val : ℂ) * S.exponent ξ‖ := Complex.norm_exp_sub_one_le htz
          _ = 2 * t.val * ‖S.exponent ξ‖ := by
                simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg t.prop.le]; ring
      calc t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re
          ≤ t.val⁻¹ * (2 * t.val * ‖S.exponent ξ‖) :=
              mul_le_mul_of_nonneg_left h_re (le_of_lt (inv_pos.mpr t.prop))
        _ = 2 * ‖S.exponent ξ‖ := by field_simp [ne_of_gt t.prop]
        _ ≤ 2 * M := by linarith
    · push Not at h
      have hψ_pos : (0 : ℝ) < ‖S.exponent ξ‖ := by
        rcases ne_or_eq (S.exponent ξ) 0 with hne | h0
        · exact norm_pos_iff.mpr hne
        · simp only [h0, norm_zero] at h; linarith
      have ht_inv : t.val⁻¹ ≤ ‖S.exponent ξ‖ :=
        (inv_le_iff_one_le_mul₀' t.prop).mpr (le_of_lt h)
      calc t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re
          ≤ t.val⁻¹ * 2 :=
              mul_le_mul_of_nonneg_left hre_le2 (le_of_lt (inv_pos.mpr t.prop))
        _ ≤ ‖S.exponent ξ‖ * 2 := by nlinarith
        _ ≤ M * 2 := by nlinarith
        _ = 2 * M := by ring
  set μ := (S.measure t : Measure ℝ)
  have : IsProbabilityMeasure μ := inferInstance
  have h_nn : ∀ (ξ x : ℝ), 0 ≤ 1 - Real.cos (ξ * x) := fun ξ x => one_sub_cos_nonneg x ξ
  have hfin_restrict : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) (2/ε))) := by
    rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ 2/ε)]
    infer_instance
  have hfubini_int : Integrable (fun p : ℝ × ℝ => 1 - Real.cos (p.1 * p.2))
      ((volume.restrict (Set.uIoc 0 (2/ε))).prod μ) :=
    Integrable.of_bound
      ((continuous_const.sub (Real.continuous_cos.comp
        (continuous_fst.mul continuous_snd))).aestronglyMeasurable)
      2
      (ae_of_all _ fun p => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (h_nn p.1 p.2)]
        linarith [Real.neg_one_le_cos (p.1 * p.2)])
  have hfubini : ∫ ξ in (0:ℝ)..(2/ε), ∫ x, (1 - Real.cos (ξ * x)) ∂μ =
      ∫ x, (∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))) ∂μ :=
    intervalIntegral_integral_swap hfubini_int
  have hrhs : ∫ ξ in (0:ℝ)..(2/ε), ∫ x, (1 - Real.cos (ξ * x)) ∂μ =
      ∫ ξ in (0:ℝ)..(2/ε), (1 - exp ((t.val : ℂ) * S.exponent ξ)).re := by
    congr 1; ext ξ
    change cosineDefectIntegral μ ξ = (1 - exp ((t.val : ℂ) * S.exponent ξ)).re
    rw [cosineDefectIntegral_eq_one_sub_charFun_re μ ξ, S.charFun_eq t ξ]
    simp
  have h_intcont : Continuous (fun x => ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x ξ => 1 - Real.cos (ξ * x))
      (by fun_prop) 0 (2/ε)
  have hint_outer : Integrable (fun x => ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))) μ :=
    Integrable.of_bound
      h_intcont.aestronglyMeasurable
      (4/ε)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg
            (intervalIntegral.integral_nonneg (by positivity) fun ξ _ => h_nn ξ x)]
        have hfx_int : IntervalIntegrable (fun ξ => 1 - Real.cos (ξ * x)) volume 0 (2/ε) :=
          (continuous_const.sub (Real.continuous_cos.comp
            (continuous_id.mul continuous_const))).intervalIntegrable 0 (2/ε)
        calc ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))
            ≤ ∫ ξ in (0:ℝ)..(2/ε), (2 : ℝ) :=
              intervalIntegral.integral_mono_on (by positivity) hfx_int intervalIntegrable_const
                (fun ξ _ => by linarith [Real.neg_one_le_cos (ξ * x)])
          _ = 4/ε := by
              rw [intervalIntegral.integral_const, smul_eq_mul]
              field_simp; ring)
  have hpointwise : ∀ x ∈ largeJumpSet ε,
      ε⁻¹ ≤ ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x)) := by
    intro x hx
    have hxε : ε ≤ |x| := mem_largeJumpSet.mp hx
    have hx_ne : x ≠ 0 := by
      intro h0; simp only [h0, abs_zero] at hxε; linarith
    have hcos_int : IntervalIntegrable (fun ξ => Real.cos (ξ * x)) volume 0 (2/ε) :=
      (Real.continuous_cos.comp (continuous_id.mul continuous_const)).intervalIntegrable 0 (2/ε)
    have hmul : ∫ ξ in (0:ℝ)..(2/ε), Real.cos (ξ * x) = Real.sin (2 * x / ε) / x := by
      rw [intervalIntegral.integral_comp_mul_right (hc := hx_ne)]
      simp only [zero_mul, smul_eq_mul]
      rw [integral_cos, Real.sin_zero, sub_zero]
      rw [show (2 : ℝ) / ε * x = 2 * x / ε from by ring]
      rw [div_eq_mul_inv (Real.sin _) x, mul_comm]
    have hcomp : ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x)) =
        2/ε - Real.sin (2 * x / ε) / x := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hcos_int,
        intervalIntegral.integral_const, smul_eq_mul, mul_one, hmul]
      ring
    rw [hcomp]
    have hsin_bd : Real.sin (2 * x / ε) / x ≤ 1/ε := by
      have habs : |Real.sin (2 * x / ε) / x| ≤ 1/ε := by
        rw [abs_div, div_le_div_iff₀ (abs_pos.mpr hx_ne) hε]
        nlinarith [Real.abs_sin_le_one (2 * x / ε)]
      linarith [le_abs_self (Real.sin (2 * x / ε) / x)]
    have h1e : (1:ℝ)/ε = ε⁻¹ := one_div ε
    have h2e : (2:ℝ)/ε = 2 * ε⁻¹ := by rw [div_eq_mul_inv]
    linarith
  have hmass : ε⁻¹ * (μ (largeJumpSet ε)).toReal ≤
      ∫ ξ in (0:ℝ)..(2/ε), (1 - exp ((t.val : ℂ) * S.exponent ξ)).re := by
    rw [← hrhs, hfubini]
    rw [show ε⁻¹ * (μ (largeJumpSet ε)).toReal =
      ∫ _ in largeJumpSet ε, ε⁻¹ ∂μ by
        rw [setIntegral_const, smul_eq_mul, Measure.real_def, mul_comm]]
    exact le_trans
      (setIntegral_mono_on integrableOn_const hint_outer.integrableOn
        (measurableSet_largeJumpSet ε) (fun x hx => hpointwise x hx))
      (setIntegral_le_integral hint_outer (ae_of_all _ (fun x =>
        intervalIntegral.integral_nonneg (by positivity) fun ξ _ => h_nn ξ x)))
  have ht_inv_nn : 0 ≤ t.val⁻¹ := le_of_lt (inv_pos.mpr t.prop)
  have hmass_t : t.val⁻¹ * ε⁻¹ * (μ (largeJumpSet ε)).toReal ≤
      ∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re := by
    have hrearrange : t.val⁻¹ * ε⁻¹ * (μ (largeJumpSet ε)).toReal =
        t.val⁻¹ * (ε⁻¹ * (μ (largeJumpSet ε)).toReal) := by ring
    rw [hrearrange]
    calc t.val⁻¹ * (ε⁻¹ * (μ (largeJumpSet ε)).toReal)
        ≤ t.val⁻¹ * (∫ ξ in (0:ℝ)..(2/ε), (1 - exp ((↑t.val : ℂ) * S.exponent ξ)).re) :=
          mul_le_mul_of_nonneg_left hmass ht_inv_nn
      _ = ∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((↑t.val : ℂ) * S.exponent ξ)).re := by
          rw [← intervalIntegral.integral_const_mul]
  have hint_exp : IntervalIntegrable
      (fun ξ => t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re) volume 0 (2/ε) :=
    ((continuous_const.sub
        (Complex.continuous_re.comp
          (Complex.continuous_exp.comp
            (continuous_const.mul S.exponent_continuous)))).const_mul _).intervalIntegrable _ _
  have hint_2M : ∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤
      ∫ ξ in (0:ℝ)..(2/ε), (2 * M) :=
    intervalIntegral.integral_mono_on (by positivity) hint_exp intervalIntegrable_const
      (fun ξ hξ => hkey ξ hξ)
  have hint_const : ∫ ξ in (0:ℝ)..(2/ε), (2 * M) = 4 * M / ε := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    field_simp [hε.ne']
    ring
  calc t.val⁻¹ * (μ (largeJumpSet ε)).toReal
      = ε * (t.val⁻¹ * ε⁻¹ * (μ (largeJumpSet ε)).toReal) := by field_simp [hε.ne', ne_of_gt t.prop]
    _ ≤ ε * (∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((↑t.val : ℂ) * S.exponent ξ)).re) := by
        exact mul_le_mul_of_nonneg_left hmass_t (le_of_lt hε)
    _ ≤ ε * (∫ ξ in (0:ℝ)..(2/ε), (2 * M)) := by
        apply mul_le_mul_of_nonneg_left hint_2M (le_of_lt hε)
    _ = ε * (4 * M / ε) := by rw [hint_const]
    _ = 4 * M := by field_simp [hε.ne']

/-- **Tail decay of the scaled mass, uniform in `t`.** For every `ε > 0` there is a
radius `R ≥ 1` beyond which the scaled mass `t⁻¹ · μ_t({|x| ≥ R})` is at most `ε`,
uniformly over all `t > 0`. Since `ψ` is continuous with `ψ 0 = 0`, its norm is small
on `[0, 2/R]` for large `R`, and `scaled_mass_bound_real_with_max` converts that into
a mass bound. This is the tightness input for the canonical-measure extraction. -/
lemma scaled_largeJumpSet_mass_le_of_large_radius (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ t : {t : ℝ // 0 < t},
      t.val⁻¹ * ((S.measure t : Measure ℝ) (largeJumpSet R)).toReal ≤ ε := by
  -- Since `ψ` is continuous with `ψ 0 = 0`, `‖ψ‖` is small on a neighbourhood of `0`.
  have hξ_exist : ∃ r : ℝ, 0 < r ∧ ∀ ξ, |ξ| < r → ‖S.exponent ξ‖ < ε/4 := by
    have htend : Tendsto (fun ξ : ℝ => ‖S.exponent ξ‖) (𝓝 0) (𝓝 0) := by
      have h1 : Tendsto S.exponent (𝓝 0) (𝓝 0) := by
        have := S.exponent_continuous.tendsto 0
        rw [S.exponent_zero] at this
        exact this
      have h2 : Tendsto (fun z : ℂ => ‖z‖) (𝓝 0) (𝓝 0) := by
        have := (continuous_norm (E := ℂ)).tendsto 0
        simpa using this
      exact h2.comp h1
    have hnhds : ∀ᶠ ξ in 𝓝 (0 : ℝ), ‖S.exponent ξ‖ < ε/4 :=
      htend.eventually (Iio_mem_nhds (by linarith))
    rw [Metric.eventually_nhds_iff] at hnhds
    obtain ⟨r, hr_pos, hr⟩ := hnhds
    exact ⟨r, hr_pos, fun ξ hξ => hr (by simpa [Real.dist_eq, sub_zero] using hξ)⟩
  obtain ⟨r, hr_pos, hr⟩ := hξ_exist
  -- Choose `R ≥ 1` large enough that `2/R < r`, so `[0, 2/R] ⊆ [0, r)`.
  set R := max (1 : ℝ) (2 / r + 1) with hR_def
  have hR_ge_one : 1 ≤ R := le_max_left _ _
  have hR_pos : 0 < R := lt_of_lt_of_le one_pos hR_ge_one
  have hR_inv : 2 / R < r := by
    have h_denom_pos : (0 : ℝ) < 2 / r + 1 := by positivity
    have h1 : 2 / R ≤ 2 / (2 / r + 1) :=
      div_le_div_of_nonneg_left (by norm_num) h_denom_pos (le_max_right _ _)
    have h2 : 2 / (2 / r + 1) < r := by
      rw [div_lt_iff₀ h_denom_pos]
      have h3 : (2 / r + 1) * r = 2 + r := by field_simp
      linarith [h3]
    linarith
  have hM_bound : ∀ ξ ∈ Set.Icc (0:ℝ) (2/R), ‖S.exponent ξ‖ ≤ ε/4 := by
    intro ξ hξ
    have h1 : |ξ| < r := by
      rw [abs_of_nonneg hξ.1]
      exact lt_of_le_of_lt hξ.2 hR_inv
    exact le_of_lt (hr ξ h1)
  refine ⟨R, hR_ge_one, fun t => ?_⟩
  calc t.val⁻¹ * ((S.measure t : Measure ℝ) (largeJumpSet R)).toReal
      ≤ 4 * (ε/4) := S.scaled_mass_bound_real_with_max R hR_pos (ε/4) (by positivity) hM_bound t
    _ = ε := by ring

end ConvolutionSemigroup

end ProbabilityTheory

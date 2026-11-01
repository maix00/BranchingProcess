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
import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Defs
import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Integrand
import MeasureTheory.Measure.Levy.JumpRegions
import all Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Lemmas.Representation.ScaledBounds
import all Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Lemmas.Representation.SmallJumpMoment
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Drift extraction in the Lévy–Khintchine proof

## Internal proof declarations

* `drift_limit` extracts a subsequential limit of the scaled first moment on a small-jump interval.
* `drift_term` transfers that real limit to the linear characteristic-exponent term.
* `charFun_sub_one_div_decomp` splits the scaled characteristic function into drift, compensated
  small-jump, and large-jump contributions.

The drift extraction and exponent decomposition take the form
\[
  \frac1{t_k}\int_{|x|<r}x\,d\mu_{t_k}(x)\longrightarrow b,
  \qquad
  \frac{\widehat\mu_t(\xi)-1}{t}
       =\text{drift term}+\text{compensated small-jump term}
          +\text{large-jump term}.
\]
-/

section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder

namespace ProbabilityTheory

namespace ConvolutionSemigroup

variable (S : ConvolutionSemigroup)

/-- The characteristic-function integrand is bounded in norm by one. -/
private lemma integrable_charFun_integrand {μ : Measure ℝ} [IsFiniteMeasure μ] (ξ : ℝ) :
    Integrable (fun x : ℝ => exp ((↑(ξ * x) : ℂ) * I)) μ :=
  Integrable.of_bound
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id')).mul_const I
      |>.cexp.aestronglyMeasurable)
    1 (ae_of_all _ fun _ => le_of_eq (Complex.norm_exp_ofReal_mul_I _))

/-- The scaled first moment on `{|x| < r}` is eventually bounded along `t_n → 0`, so
Bolzano-Weierstrass gives a convergent subsequence.  Boundedness follows from the sin
decomposition: `t⁻¹∫_{|x|<r} x = Im((charFun-1)/t) − t⁻¹∫_{largeJumpSet r} sin + t⁻¹∫_{|x|<r}(x-sin)`,
where the three terms are respectively eventually bounded (via charFun limit), globally bounded
(via scaled_mass_bound_real at radius r), and eventually bounded (via the x²/2 bound + the
second-moment dominated through `{|x|<r} ⊆ smallJumpSet`). -/
lemma drift_limit
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {t_seq : ℕ → {t : ℝ // 0 < t}} (ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0)) :
    ∃ b : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
    Tendsto (fun n =>
      (t_seq (φ n)).val⁻¹ * ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq (φ n)) : Measure ℝ))
    atTop (𝓝 b) := by
  -- The radius-`r` open ball: measurability and complement identity.
  have hmeas_ball : MeasurableSet {x : ℝ | |x| < r} :=
    measurableSet_lt continuous_abs.measurable measurable_const
  have hball_compl : {x : ℝ | |x| < r} = (largeJumpSet r)ᶜ := by
    ext x; simp only [largeJumpSet, Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
  have hsubset : {x : ℝ | |x| < r} ⊆ smallJumpSet :=
    fun x hx => mem_smallJumpSet.mpr (lt_of_lt_of_le hx hr1)
  -- Pull `t_seq` back through the comap filter used by `charFun_scaled_limit`.
  have htseq_filter : Tendsto t_seq atTop (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) := by
    rw [Filter.tendsto_comap_iff]
    exact tendsto_nhdsWithin_iff.mpr ⟨ht, Filter.Eventually.of_forall (fun n => (t_seq n).prop)⟩
  -- Convergence of the charFun quotient Im part at ξ = 1.
  have hcf_tend : Tendsto
      (fun n => (charFun (S.measure (t_seq n) : Measure ℝ) 1 - 1) /
        ↑(t_seq n).val)
      atTop (𝓝 (S.exponent 1)) :=
    (S.charFun_scaled_limit 1).comp htseq_filter
  -- The Im of the charFun quotient converges to Im(S.exponent 1), hence eventually bounded.
  have hIm_tend : Tendsto
      (fun n => ((charFun (S.measure (t_seq n) : Measure ℝ) 1 - 1) /
        ↑(t_seq n).val).im)
      atTop (𝓝 (S.exponent 1).im) :=
    (Complex.continuous_im.tendsto _).comp hcf_tend
  -- Eventually |Im(charFun/t)| ≤ |Im(ψ(1))| + 1.
  have hIm_bdd : ∀ᶠ n in atTop, |((charFun (S.measure (t_seq n) : Measure ℝ) 1 - 1) /
      ↑(t_seq n).val).im| ≤ |(S.exponent 1).im| + 1 := by
    have h := hIm_tend.eventually (Metric.ball_mem_nhds (S.exponent 1).im one_pos)
    filter_upwards [h] with n hn
    simp only [Real.dist_eq] at hn
    linarith [abs_sub_abs_le_abs_sub
      ((charFun (S.measure (t_seq n) : Measure ℝ) 1 - 1) / ↑(t_seq n).val).im
      (S.exponent 1).im]
  -- Im((charFun μ 1 - 1)/t) = t⁻¹ * ∫ sin x dμ  (for probability measure μ).
  have hIm_eq : ∀ n,
      ((charFun (S.measure (t_seq n) : Measure ℝ) 1 - 1) / ↑(t_seq n).val).im =
      (t_seq n).val⁻¹ * ∫ x, Real.sin x ∂(S.measure (t_seq n) : Measure ℝ) := by
    intro n
    set t := (t_seq n).val
    set μ : Measure ℝ := (S.measure (t_seq n) : Measure ℝ)
    have : IsProbabilityMeasure μ := (S.measure (t_seq n)).prop
    have hcf : charFun μ (1 : ℝ) = ∫ x : ℝ, Complex.exp (↑x * I) ∂μ := by
      rw [charFun_apply_real]; congr 1; ext x; push_cast; ring_nf
    have hint1 : Integrable (fun x : ℝ => Complex.exp (↑x * I)) μ := by
      convert integrable_charFun_integrand (μ := μ) 1 using 2; push_cast; ring_nf
    have hnum : charFun μ (1 : ℝ) - 1 = ∫ x : ℝ, (Complex.exp (↑x * I) - 1) ∂μ := by
      rw [hcf]
      conv_lhs => rw [show (1 : ℂ) = ∫ _ : ℝ, (1 : ℂ) ∂μ by simp [integral_const]]
      rw [← integral_sub hint1 (integrable_const 1)]
    rw [hnum, Complex.div_ofReal_im,
        show (∫ x : ℝ, (Complex.exp (↑x * I) - 1) ∂μ).im =
            ∫ x : ℝ, (Complex.exp (↑x * I) - 1).im ∂μ from
            ((RCLike.imCLM (K := ℂ)).integral_comp_comm
              (hint1.sub (integrable_const 1))).symm]
    simp only [Complex.sub_im, Complex.one_im, sub_zero, Complex.exp_ofReal_mul_I_im]
    rw [div_eq_inv_mul]
  -- Global bound on t⁻¹ * μ_t(largeJumpSet r) via scaled_mass_bound_real.
  obtain ⟨C_large, hC_large⟩ := S.scaled_mass_bound_real r hr
  -- Eventually bounded second moment: t⁻¹ ∫_small x² ≤ C₂.
  obtain ⟨C₂, hC₂_pos, hC₂⟩ := S.scaled_second_moment_bounded_along_seq ht
  -- The sequence a_n := t_n⁻¹ ∫_{|x|<r} x dμ_n is eventually in a compact interval.
  set a : ℕ → ℝ := fun n =>
    (t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ)
  have ha_bdd : ∀ᶠ n in atTop, a n ∈ Set.Icc (-(|(S.exponent 1).im| + 1 + C_large + C₂))
      (|(S.exponent 1).im| + 1 + C_large + C₂) := by
    filter_upwards [hIm_bdd, hC₂] with n hIm hC₂n
    simp only [Set.mem_Icc]
    -- sin-decomposition: a_n = Im_n + small_(x-sin) - large_sin
    -- where Im_n := Im((charFun-1)/t_n)
    have hμ_prob : IsProbabilityMeasure (S.measure (t_seq n) : Measure ℝ) :=
      (S.measure (t_seq n)).prop
    have t_pos := (t_seq n).prop
    -- Integrability lemmas
    have hint_sin : Integrable (fun x => Real.sin x) (S.measure (t_seq n) : Measure ℝ) :=
      Integrable.of_bound Real.continuous_sin.aestronglyMeasurable 1
        (ae_of_all _ fun x => by simp [abs_le.mpr ⟨Real.neg_one_le_sin x,
          Real.sin_le_one x⟩])
    have hint_x_small : IntegrableOn (fun x => x) {x | |x| < r}
        (S.measure (t_seq n) : Measure ℝ) :=
      IntegrableOn.of_bound (measure_lt_top _ _)
        continuous_id.aestronglyMeasurable.restrict 1
        ((ae_restrict_mem hmeas_ball).mono
          (fun x hx => by
            simp only [Real.norm_eq_abs]
            exact (lt_of_lt_of_le hx hr1).le))
    have hint_sin_small : IntegrableOn (fun x => Real.sin x) {x | |x| < r}
        (S.measure (t_seq n) : Measure ℝ) :=
      hint_sin.integrableOn
    have hint_xsin_small : IntegrableOn (fun x => x - Real.sin x) {x | |x| < r}
        (S.measure (t_seq n) : Measure ℝ) :=
      (hint_x_small.sub hint_sin_small)
    -- ∫_{|x|<r} x = ∫_{|x|<r} (x - sin x) + ∫_{|x|<r} sin x
    have hsplit_x : ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ) =
        ∫ x in {x | |x| < r}, (x - Real.sin x) ∂(S.measure (t_seq n) : Measure ℝ) +
        ∫ x in {x | |x| < r}, Real.sin x ∂(S.measure (t_seq n) : Measure ℝ) := by
      rw [← integral_add hint_xsin_small hint_sin_small]
      congr 1; ext x; ring
    -- ∫_{|x|<r} sin x = ∫ sin x - ∫_{largeJumpSet r} sin x (ball = (largeJumpSet r)ᶜ)
    have hsplit_sin : ∫ x in {x | |x| < r}, Real.sin x ∂(S.measure (t_seq n) : Measure ℝ) =
        ∫ x, Real.sin x ∂(S.measure (t_seq n) : Measure ℝ) -
        ∫ x in largeJumpSet r, Real.sin x ∂(S.measure (t_seq n) : Measure ℝ) := by
      rw [hball_compl,
          ← integral_add_compl (measurableSet_largeJumpSet r) hint_sin]
      ring
    -- a_n = t⁻¹∫_{|x|<r}(x-sin) + Im(charFun/t) - t⁻¹∫_{largeJumpSet r} sin
    have ha_eq : a n = (t_seq n).val⁻¹ *
        ∫ x in {x | |x| < r}, (x - Real.sin x) ∂(S.measure (t_seq n) : Measure ℝ) +
        ((charFun (S.measure (t_seq n) : Measure ℝ) 1 - 1) / ↑(t_seq n).val).im -
        (t_seq n).val⁻¹ *
        ∫ x in largeJumpSet r, Real.sin x ∂(S.measure (t_seq n) : Measure ℝ) := by
      simp only [a, hIm_eq n, hsplit_x, hsplit_sin]
      ring
    -- Bound |t⁻¹∫_{largeJumpSet r} sin x|: each |sin x| ≤ 1, so ≤ t⁻¹ * μ(largeJumpSet r) ≤ C_large
    have hL : |(t_seq n).val⁻¹ *
        ∫ x in largeJumpSet r, Real.sin x ∂(S.measure (t_seq n) : Measure ℝ)| ≤ C_large := by
      have hbound : ‖∫ x in largeJumpSet r, Real.sin x ∂(S.measure (t_seq n) : Measure ℝ)‖ ≤
          ((S.measure (t_seq n) : Measure ℝ) (largeJumpSet r)).toReal := by
        have h := norm_setIntegral_le_of_norm_le_const
            (measure_lt_top (S.measure (t_seq n) : Measure ℝ) (largeJumpSet r))
            (fun x _ => show ‖Real.sin x‖ ≤ 1 by
              simp only [Real.norm_eq_abs]
              exact abs_le.mpr ⟨by linarith [Real.neg_one_le_sin x], Real.sin_le_one x⟩)
        simpa [one_mul, measureReal_def] using h
      rw [abs_mul, abs_of_pos (inv_pos.mpr t_pos)]
      calc (t_seq n).val⁻¹ * |∫ x in largeJumpSet r, Real.sin x ∂(S.measure (t_seq n) : Measure ℝ)|
          ≤ (t_seq n).val⁻¹ * ((S.measure (t_seq n) : Measure ℝ) (largeJumpSet r)).toReal := by
            apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt t_pos))
            rwa [Real.norm_eq_abs] at hbound
        _ ≤ C_large := hC_large (t_seq n)
    -- x² integrable on smallJumpSet (bounded by 1, finite measure) — for the domination step.
    have hint_sq_small : IntegrableOn (fun x => x ^ 2) smallJumpSet
        (S.measure (t_seq n) : Measure ℝ) :=
      integrableOn_sq_smallJumpSet _
    -- Domination: ∫_{|x|<r} x² ≤ ∫_small x²  (since {|x|<r} ⊆ smallJumpSet, x² ≥ 0).
    have hdom : ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ) ≤
        ∫ x in smallJumpSet, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ) :=
      setIntegral_mono_set hint_sq_small (ae_of_all _ fun x => sq_nonneg x)
        (LE.le.eventuallyLE hsubset)
    -- Bound |t⁻¹∫_{|x|<r} (x - sin x)|: |x - sin x| ≤ x²/2 on {|x|<r}, then dominate by smallJumpSet.
    have hS : |(t_seq n).val⁻¹ *
        ∫ x in {x | |x| < r}, (x - Real.sin x) ∂(S.measure (t_seq n) : Measure ℝ)| ≤ C₂ := by
      have habs_bound : ∀ x ∈ {x : ℝ | |x| < r}, |x - Real.sin x| ≤ x ^ 2 / 2 :=
        fun x hx => by
          have hxabs : |x| ≤ 1 := le_of_lt (lt_of_lt_of_le hx hr1)
          calc
            |x - Real.sin x| ≤ |x| ^ 3 / 6 := Real.abs_sub_sin_le x
            _ ≤ |x| ^ 2 / 2 := by
              have h := mul_nonneg (sq_nonneg |x|) (sub_nonneg.mpr (by linarith))
              nlinarith
            _ = x ^ 2 / 2 := by rw [sq_abs]
      have hxsin_norm : ‖∫ x in {x | |x| < r}, (x - Real.sin x)
            ∂(S.measure (t_seq n) : Measure ℝ)‖ ≤
          (1/2) * ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ) := by
        calc ‖∫ x in {x | |x| < r}, (x - Real.sin x) ∂(S.measure (t_seq n) : Measure ℝ)‖
            ≤ ∫ x in {x | |x| < r}, ‖x - Real.sin x‖ ∂(S.measure (t_seq n) : Measure ℝ) :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ x in {x | |x| < r}, x ^ 2 / 2 ∂(S.measure (t_seq n) : Measure ℝ) := by
              apply setIntegral_mono_on hint_xsin_small.norm
              · exact ((hint_sq_small.mono_set hsubset).div_const 2)
              · exact hmeas_ball
              · intro x hx
                simp only [Real.norm_eq_abs]
                exact habs_bound x hx
          _ = (1/2) * ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ) := by
              rw [← integral_const_mul]; congr 1; funext x; ring
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr t_pos)] at *
      calc (t_seq n).val⁻¹ *
            ‖∫ x in {x | |x| < r}, (x - Real.sin x) ∂(S.measure (t_seq n) : Measure ℝ)‖
          ≤ (t_seq n).val⁻¹ *
              ((1/2) * ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ)) :=
            mul_le_mul_of_nonneg_left hxsin_norm (inv_nonneg.mpr (le_of_lt t_pos))
        _ = (1/2) * ((t_seq n).val⁻¹ *
              ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ)) := by ring
        _ ≤ (1/2) * ((t_seq n).val⁻¹ *
              ∫ x in smallJumpSet, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul_of_nonneg_left hdom (inv_nonneg.mpr (le_of_lt t_pos))
        _ ≤ (1/2) * C₂ := by
            apply mul_le_mul_of_nonneg_left hC₂n (by norm_num)
        _ ≤ C₂ := by linarith [hC₂_pos]
    constructor
    · linarith [ha_eq, (abs_le.mp hS).1, (abs_le.mp hIm).1, (abs_le.mp hL).2]
    · linarith [ha_eq, (abs_le.mp hS).2, (abs_le.mp hIm).2, (abs_le.mp hL).1]
  -- Apply Bolzano-Weierstrass to `a`.
  obtain ⟨b, -, φ, hφ_mono, hb⟩ :=
    isCompact_Icc.tendsto_subseq' ha_bdd.frequently
  exact ⟨b, φ, hφ_mono, hb⟩

/-- The drift term contributes `b * ξ * I` to the decomposition.
Factor out `ξ * I` from the integral of `x * ξ * I`. -/
lemma drift_term (ξ : ℝ) {r : ℝ}
    {t_seq : ℕ → {t : ℝ // 0 < t}} (_ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0))
    {b : ℝ} (hb : Tendsto (fun n =>
      (t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ))
    atTop (𝓝 b)) :
    Tendsto (fun n =>
      ((t_seq n).val⁻¹ : ℂ) *
      ∫ x in {x | |x| < r}, (↑x * ↑ξ * I) ∂(S.measure (t_seq n) : Measure ℝ))
    atTop (𝓝 (↑b * ↑ξ * I)) := by
  -- Step 1: Rewrite each summand to factor out the constant (↑ξ * I)
  suffices h : Tendsto (fun n =>
      ↑((t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ)) *
      ((↑ξ : ℂ) * I)) atTop (𝓝 (↑b * ↑ξ * I)) by
    refine h.congr (fun n => ?_)
    -- Show the two expressions are equal
    have : ∫ x in {x | |x| < r}, ((↑x : ℂ) * ↑ξ * I) ∂(S.measure (t_seq n) : Measure ℝ) =
        ↑(∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ)) * (↑ξ * I) := by
      simp_rw [mul_assoc]
      have : ∀ x : ℝ, (↑x : ℂ) * ((↑ξ : ℂ) * I) = (↑x : ℂ) • ((↑ξ : ℂ) * I) := by
        intro x; rw [smul_eq_mul]
      simp_rw [this]
      rw [integral_smul_const]
      congr 1
      exact integral_ofReal
    rw [this]; push_cast; ring
  -- Step 2: ↑(t⁻¹ * ∫) * (↑ξ * I) → ↑b * (↑ξ * I) = ↑b * ↑ξ * I
  rw [show (↑b : ℂ) * ↑ξ * I = ↑b * (↑ξ * I) from by ring]
  exact Filter.Tendsto.mul_const ((↑ξ : ℂ) * I) hb.ofReal

/-- **Per-`t` algebraic identity.** Decomposes `(charFun μ_t ξ − 1) / t` into the three
contributions that appear in the Lévy-Khintchine formula: the small-jump drift integral
`iξ · t⁻¹·∫_smallJumpSet x dμ`, the small-jump compensated remainder `t⁻¹·∫_smallJumpSet
(exp(ixξ)−1−ixξ) dμ`, and the large-jump integral `t⁻¹·∫_{largeJumpSet 1}(exp(ixξ)−1) dμ`.

This is the algebraic backbone of `psi_eq_levyKhintchine_formula`: the LK assembly
chains subsequential limits of the three RHS terms (`drift_term`, the to-be-proved
small/large jump identifications) and matches against `charFun_scaled_limit` to
conclude the formula. -/
lemma charFun_sub_one_div_decomp (t : {t : ℝ // 0 < t}) (ξ : ℝ)
    {r : ℝ} (hr1 : r ≤ 1) :
    (charFun (S.measure t : Measure ℝ) ξ - 1) / (↑t.val : ℂ) =
      (↑t.val⁻¹ : ℂ) *
          ∫ x in {x | |x| < r}, ((↑x : ℂ) * ↑ξ * I) ∂(S.measure t : Measure ℝ)
      + (↑t.val⁻¹ : ℂ) *
          ∫ x in {x | |x| < r}, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I)
            ∂(S.measure t : Measure ℝ)
      + (↑t.val⁻¹ : ℂ) *
          ∫ x in largeJumpSet r, (exp ((↑x : ℂ) * ↑ξ * I) - 1)
            ∂(S.measure t : Measure ℝ) := by
  set μ : Measure ℝ := (S.measure t : Measure ℝ) with hμ_def
  have hmeas_ball : MeasurableSet {x : ℝ | |x| < r} :=
    measurableSet_lt continuous_abs.measurable measurable_const
  have hball_compl : {x : ℝ | |x| < r} = (largeJumpSet r)ᶜ := by
    ext x; simp only [largeJumpSet, Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
  -- Integrability of x ↦ exp(↑x*↑ξ*I) against μ.
  have hexp_int : Integrable (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I)) μ := by
    refine (integrable_charFun_integrand (μ := μ) ξ).congr ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    push_cast; ring_nf
  -- Integrability of x ↦ exp(↑x*↑ξ*I) − 1.
  have hsub_int : Integrable (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1) μ :=
    hexp_int.sub (integrable_const _)
  -- Integrability of x ↦ ↑x*↑ξ*I on {|x|<r} (bounded by |ξ|).
  have hxi_int : IntegrableOn (fun x : ℝ => (↑x : ℂ) * ↑ξ * I) {x | |x| < r} μ := by
    refine (integrable_const (|ξ|)).mono' ?_ ?_
    · exact ((Complex.measurable_ofReal.mul measurable_const).mul
        measurable_const).aestronglyMeasurable
    · refine (ae_restrict_iff' hmeas_ball).mpr ?_
      filter_upwards with x hx
      have hnorm : ‖((↑x : ℂ) * ↑ξ * I)‖ = |x| * |ξ| := by
        rw [show ((↑x : ℂ) * ↑ξ * I) = ((↑(x * ξ) : ℂ)) * I from by
              push_cast; ring,
            norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_mul]
      rw [hnorm]
      calc |x| * |ξ| ≤ 1 * |ξ| :=
            mul_le_mul_of_nonneg_right (le_of_lt (lt_of_lt_of_le hx hr1)) (abs_nonneg _)
        _ = |ξ| := one_mul _
  -- Integrability of the compensated remainder on {|x|<r}.
  have hrem_int : IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) {x | |x| < r} μ :=
    (hsub_int.integrableOn).sub hxi_int
  -- Step 1: (charFun μ ξ − 1) = ∫ (exp(ixξ) − 1) dμ.
  have h_one : (∫ _ : ℝ, (1 : ℂ) ∂μ) = 1 := by simp
  have h1 : charFun μ ξ - 1 = ∫ x, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂μ := by
    have hcf : charFun μ ξ = ∫ x, exp ((↑x : ℂ) * ↑ξ * I) ∂μ := by
      rw [charFun_apply_real]; congr 1; ext x; congr 1; ring
    calc charFun μ ξ - 1
        = (∫ x, exp ((↑x : ℂ) * ↑ξ * I) ∂μ) - ∫ _ : ℝ, (1 : ℂ) ∂μ := by
            rw [hcf, h_one]
      _ = ∫ x, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂μ :=
          (integral_sub hexp_int (integrable_const 1)).symm
  -- Step 2: split via {|x|<r}/largeJumpSet r.
  have hcompl_ball : ({x : ℝ | |x| < r})ᶜ = largeJumpSet r := by
    rw [hball_compl, compl_compl]
  have h2 : ∫ x, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂μ
      = ∫ x in {x | |x| < r}, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂μ
        + ∫ x in largeJumpSet r, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂μ := by
    have hs := (integral_add_compl hmeas_ball hsub_int).symm
    rw [hcompl_ball] at hs
    exact hs
  -- Step 3: split the {|x|<r} integral additively.
  have h3 : ∫ x in {x | |x| < r}, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂μ
      = ∫ x in {x | |x| < r}, ((↑x : ℂ) * ↑ξ * I) ∂μ
        + ∫ x in {x | |x| < r}, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) ∂μ := by
    rw [← integral_add hxi_int hrem_int]
    refine setIntegral_congr_fun hmeas_ball (fun x _ => ?_)
    ring
  rw [h1, h2, h3]
  push_cast
  ring

end ConvolutionSemigroup

end ProbabilityTheory

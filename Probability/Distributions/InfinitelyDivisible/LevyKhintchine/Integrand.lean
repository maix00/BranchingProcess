/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

public import MeasureTheory.Measure.Levy.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Analysis.Fourier.ConditionallyPositiveDefinite.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Compensated Integrand for the Lévy-Khintchine Formula

The **compensated integrand** is the function
`f(ξ, x) = exp(ixξ) - 1 - ixξ · 1_{|x| < 1}`
which appears in the Lévy-Khintchine representation of infinitely divisible distributions.

## Public declarations

* `ProbabilityTheory.levyCompensatedIntegrand ξ x` is
  $e^{i x\xi}-1-i x\xi\mathbf 1_{\{|x|<1\}}$. Its defining equation is
  `levyCompensatedIntegrand_def`, and `levyCompensatedIntegrand_zero_right`
  and `levyCompensatedIntegrand_zero_left` state that it vanishes at `x = 0`
  and `ξ = 0`, respectively.

* `levyCompensatedIntegrand_eq_exp_sub_one_of_one_le_abs` states
  $f(\xi,x)=e^{i x\xi}-1$ when $1\le |x|$; `conj_levyCompensatedIntegrand`
  states $\overline{f(\xi,x)}=f(-\xi,x)$.
* `measurable_levyCompensatedIntegrand` proves measurability in `x` for fixed
  `ξ`; `continuous_levyCompensatedIntegrand_fst` proves continuity in `ξ` for
  fixed `x`.
* `norm_levyCompensatedIntegrand_le_two` gives $\|f(\xi,x)\|\le2$ when
  $1\le|x|$, and `norm_levyCompensatedIntegrand_le` gives
  $\|f(\xi,x)\|\le(2+3\xi^2)\min(1,x^2)$ for all `x, ξ`.
* If `ν` is a Lévy measure, `lintegral_enorm_levyCompensatedIntegrand_lt_top`
  proves $\int\|f(\xi,x)\|\,d\nu(x)<\infty$, and
  `integrable_levyCompensatedIntegrand` gives Bochner integrability.
  `integral_levyCompensatedIntegrand_eq_small_add_large` splits the integral
  over $(-1,1)$ and $\{|x|\ge1\}$ into compensated and uncompensated parts.
* `cpd_levyCompensatedIntegrand_fixed` proves $\xi\mapsto f(\xi,x)$ is
  conditionally positive definite for each `x`; `cpd_integral_levyCompensatedIntegrand`
  proves the same for its integral against a Lévy measure.
* `continuous_integral_levyCompensatedIntegrand` proves continuity in `ξ` of
  that integral, and `hermitian_integral_levyCompensatedIntegrand` states its
  Hermitian symmetry under `ξ ↦ -ξ`.
-/

@[expose] public section

open MeasureTheory Complex ENNReal Set
open Filter Topology
open scoped NNReal ENNReal ComplexConjugate

namespace ProbabilityTheory

/-- The **compensated integrand** for the Lévy-Khintchine formula:
`f(ξ, x) = exp(ixξ) - 1 - ixξ · 1_{|x| < 1}`. -/
noncomputable def levyCompensatedIntegrand (ξ x : ℝ) : ℂ :=
  exp (↑x * ↑ξ * I) - 1 - ↑x * ↑ξ * I * if |x| < 1 then 1 else 0

@[simp]
theorem levyCompensatedIntegrand_def (ξ x : ℝ) :
    levyCompensatedIntegrand ξ x =
      exp (↑x * ↑ξ * I) - 1 - ↑x * ↑ξ * I * if |x| < 1 then 1 else 0 :=
  rfl

/-- The compensated integrand vanishes at `x = 0`. -/
@[simp]
theorem levyCompensatedIntegrand_zero_right (ξ : ℝ) :
    levyCompensatedIntegrand ξ 0 = 0 := by
  simp [levyCompensatedIntegrand]

/-- The compensated integrand vanishes at `ξ = 0`. -/
@[simp]
theorem levyCompensatedIntegrand_zero_left (x : ℝ) :
    levyCompensatedIntegrand 0 x = 0 := by
  simp [levyCompensatedIntegrand]

/-- Outside the unit ball, the compensation term vanishes:
`f(ξ, x) = exp(i x ξ) - 1` when `1 ≤ |x|`. -/
theorem levyCompensatedIntegrand_eq_exp_sub_one_of_one_le_abs {ξ x : ℝ}
    (hx : 1 ≤ |x|) :
    levyCompensatedIntegrand ξ x = exp (↑x * ↑ξ * I) - 1 := by
  simp [levyCompensatedIntegrand, show ¬(|x| < 1) from not_lt.mpr hx]

/-- Complex conjugation reflects the compensated integrand's frequency:
`conj (f ξ x) = f (-ξ) x`. -/
theorem conj_levyCompensatedIntegrand (ξ x : ℝ) :
    starRingEnd ℂ (levyCompensatedIntegrand ξ x) = levyCompensatedIntegrand (-ξ) x := by
  have hww : starRingEnd ℂ ((↑x : ℂ) * ↑ξ * I) = (↑x : ℂ) * ↑(-ξ) * I := by
    simp only [map_mul, conj_ofReal, conj_I]
    push_cast; ring
  simp only [levyCompensatedIntegrand]
  by_cases hx : |x| < 1
  · simp only [ite_eq_left hx, mul_one, map_sub, map_one, ← exp_conj, hww]
  · simp only [ite_eq_right hx, mul_zero, sub_zero, map_sub, map_one, ← exp_conj, hww]

/-- The compensated integrand is measurable in `x` for fixed `ξ`. -/
@[fun_prop]
theorem measurable_levyCompensatedIntegrand (ξ : ℝ) :
    Measurable (levyCompensatedIntegrand ξ) := by
  unfold levyCompensatedIntegrand
  apply Measurable.sub
  · apply Measurable.sub
    · exact (((Complex.measurable_ofReal).mul measurable_const).mul measurable_const).cexp
    · exact measurable_const
  · apply Measurable.mul
    · exact (Complex.measurable_ofReal.mul measurable_const).mul measurable_const
    · exact measurable_const.ite
        (isOpen_Iio.preimage continuous_abs |>.measurableSet) measurable_const

/-- For `|x| ≥ 1`, `‖f(ξ,x)‖ ≤ 2`. -/
theorem norm_levyCompensatedIntegrand_le_two {ξ x : ℝ} (hx : 1 ≤ |x|) :
    ‖levyCompensatedIntegrand ξ x‖ ≤ 2 := by
  simp only [levyCompensatedIntegrand, not_lt.mpr hx, ite_false, mul_zero, sub_zero]
  calc ‖exp (↑x * ↑ξ * I) - 1‖
      ≤ ‖exp (↑x * ↑ξ * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 1 + 1 := by
        rw [show (↑x : ℂ) * ↑ξ * I = ↑(x * ξ) * I from by push_cast; ring,
          norm_exp_ofReal_mul_I, norm_one]
    _ = 2 := by ring

/-- The compensated integrand norm is bounded by `(2 + 3 * ξ²) · min(1, x²)`. -/
theorem norm_levyCompensatedIntegrand_le (ξ x : ℝ) :
    ‖levyCompensatedIntegrand ξ x‖ ≤ (2 + 3 * ξ ^ 2) * min 1 (x ^ 2) := by
  by_cases hx : |x| < 1
  · -- Case |x| < 1: indicator is 1, f(ξ,x) = exp(ixξ) - 1 - ixξ
    have hx2 : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).mpr hx
    have hmin : min (1 : ℝ) (x ^ 2) = x ^ 2 := min_eq_right (le_of_lt hx2)
    rw [hmin]
    simp only [levyCompensatedIntegrand, hx, ite_true, mul_one]
    -- Now goal: ‖exp(↑x * ↑ξ * I) - 1 - ↑x * ↑ξ * I‖ ≤ (2 + 3 * ξ²) * x²
    set z : ℂ := ↑x * ↑ξ * I with hz_def
    have hz_eq : z = ↑(x * ξ) * I := by push_cast; ring
    have hz_norm : ‖z‖ = |x * ξ| := by
      rw [hz_eq, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    by_cases hxξ : |x * ξ| ≤ 1
    · -- Sub-case |xξ| ≤ 1: use norm_exp_sub_one_sub_id_le
      have hle : ‖z‖ ≤ 1 := by rw [hz_norm]; exact hxξ
      have htaylor : ‖exp z - 1 - z‖ ≤ ‖z‖ ^ 2 := norm_exp_sub_one_sub_id_le hle
      calc ‖exp z - 1 - z‖ ≤ ‖z‖ ^ 2 := htaylor
        _ = (x * ξ) ^ 2 := by rw [hz_norm, sq_abs]
        _ = x ^ 2 * ξ ^ 2 := by ring
        _ ≤ (2 + 3 * ξ ^ 2) * x ^ 2 := by nlinarith [sq_nonneg ξ, sq_nonneg x]
    · -- Sub-case |xξ| > 1: use triangle inequality
      push Not at hxξ
      have hexp : ‖exp z‖ = 1 := by rw [hz_eq]; exact norm_exp_ofReal_mul_I _
      -- Triangle: ‖exp(z) - 1 - z‖ ≤ ‖exp(z) - 1‖ + ‖z‖ ≤ 2 + |xξ|
      have htri : ‖exp z - 1 - z‖ ≤ 2 + |x * ξ| := by
        calc ‖exp z - 1 - z‖
            = ‖(exp z - 1) - z‖ := by ring_nf
          _ ≤ ‖exp z - 1‖ + ‖z‖ := norm_sub_le _ _
          _ ≤ (‖exp z‖ + ‖(1 : ℂ)‖) + ‖z‖ := by
              gcongr; exact norm_sub_le _ _
          _ = 2 + |x * ξ| := by rw [hexp, norm_one, hz_norm]; ring
      -- 2 + t ≤ 3t² when t ≥ 1 (since 3t² - t - 2 = (3t+2)(t-1) ≥ 0)
      have h3 : 2 + |x * ξ| ≤ 3 * (x * ξ) ^ 2 := by nlinarith [sq_abs (x * ξ)]
      calc ‖exp z - 1 - z‖ ≤ 2 + |x * ξ| := htri
        _ ≤ 3 * (x * ξ) ^ 2 := h3
        _ = 3 * ξ ^ 2 * x ^ 2 := by ring
        _ ≤ (2 + 3 * ξ ^ 2) * x ^ 2 := by nlinarith [sq_nonneg x]
  · -- Case |x| ≥ 1: indicator is 0
    push Not at hx
    have hmin : min (1 : ℝ) (x ^ 2) = 1 :=
      min_eq_left ((one_le_sq_iff_one_le_abs x).mpr hx)
    rw [hmin]
    calc ‖levyCompensatedIntegrand ξ x‖ ≤ 2 := norm_levyCompensatedIntegrand_le_two hx
      _ ≤ (2 + 3 * ξ ^ 2) * 1 := by nlinarith [sq_nonneg ξ]

/-- The Lebesgue integral of `‖levyCompensatedIntegrand ξ ·‖ₑ` against a Lévy measure is finite. -/
theorem lintegral_enorm_levyCompensatedIntegrand_lt_top
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν) (ξ : ℝ) :
    ∫⁻ x, ‖levyCompensatedIntegrand ξ x‖ₑ ∂ν < ⊤ := by
  have hC : (0 : ℝ) ≤ 2 + 3 * ξ ^ 2 := by positivity
  calc ∫⁻ x, ‖levyCompensatedIntegrand ξ x‖ₑ ∂ν
      = ∫⁻ x, ENNReal.ofReal ‖levyCompensatedIntegrand ξ x‖ ∂ν := by
        simp only [ofReal_norm]
    _ ≤ ∫⁻ x, ENNReal.ofReal ((2 + 3 * ξ ^ 2) * min 1 (x ^ 2)) ∂ν := by
        apply lintegral_mono
        intro x
        exact ENNReal.ofReal_le_ofReal (norm_levyCompensatedIntegrand_le ξ x)
    _ = ∫⁻ x, ENNReal.ofReal (2 + 3 * ξ ^ 2) * ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
        congr 1; ext x
        rw [← ENNReal.ofReal_mul hC]
    _ = ENNReal.ofReal (2 + 3 * ξ ^ 2) * ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.mul_lt_top ofReal_lt_top hν.lintegral_min_one_sq_lt_top

/-- The compensated integrand is Bochner integrable against a Lévy measure. -/
theorem integrable_levyCompensatedIntegrand
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν) (ξ : ℝ) :
    Integrable (levyCompensatedIntegrand ξ) ν :=
  ⟨(measurable_levyCompensatedIntegrand ξ).aestronglyMeasurable,
    lintegral_enorm_levyCompensatedIntegrand_lt_top hν ξ⟩

/-- The Lévy–Khintchine jump integral splits at radius 1: the compensated part over
`(-1, 1)` plus the uncompensated part over `{|x| ≥ 1}`. -/
theorem integral_levyCompensatedIntegrand_eq_small_add_large
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν) (ξ : ℝ) :
    ∫ x, levyCompensatedIntegrand ξ x ∂ν
      = (∫ x in Set.Ioo (-1) 1,
          (Complex.exp (x * ξ * Complex.I) - 1 - x * ξ * Complex.I) ∂ν)
        + ∫ x in {x : ℝ | 1 ≤ |x|}, (Complex.exp (x * ξ * Complex.I) - 1) ∂ν := by
  have hcompl : (Set.Ioo (-1 : ℝ) 1)ᶜ = {x : ℝ | 1 ≤ |x|} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt, Set.mem_ofPred_eq]
    constructor
    · rintro (h | h)
      · exact le_trans (by linarith) (neg_le_abs x)
      · exact le_trans h (le_abs_self x)
    · intro h
      rcases le_total 0 x with hx | hx
      · right; rwa [abs_of_nonneg hx] at h
      · left; rw [abs_of_nonpos hx] at h; linarith
  rw [← integral_add_compl measurableSet_Ioo (integrable_levyCompensatedIntegrand hν ξ)]
  congr 1
  · apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    rw [Set.mem_Ioo] at hx
    simp only [levyCompensatedIntegrand, abs_lt.mpr hx, ite_true, mul_one]
  · rw [hcompl]
    apply setIntegral_congr_fun (hcompl ▸ measurableSet_Ioo.compl)
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    simp only [levyCompensatedIntegrand, not_lt.mpr hx, ite_false, mul_zero, sub_zero]

/-- For fixed `x`, the compensated integrand `ξ ↦ f(ξ, x)` is conditionally positive
definite. It splits as `(exp(ixξ) - 1) + (-x·1_{|x|<1})·ξ·I`: the first summand is
conditionally positive definite via `IsPositiveDefinite.exp_ofReal_mul` and `cpd_sub_one`,
the second via `IsConditionallyPositiveDefinite.imaginary_additive` (the indicator coefficient
is independent of `ξ`). -/
theorem cpd_levyCompensatedIntegrand_fixed (x : ℝ) :
    IsConditionallyPositiveDefinite (fun ξ => levyCompensatedIntegrand ξ x) := by
  have hexp : IsConditionallyPositiveDefinite
      (fun ξ : ℝ => Complex.exp ((x : ℂ) * (ξ : ℂ) * I) - 1) :=
    IsPositiveDefinite.cpd_sub_one (IsPositiveDefinite.exp_ofReal_mul x)
  have hlin : IsConditionallyPositiveDefinite
      (fun ξ : ℝ => ((if |x| < 1 then -x else 0 : ℝ) : ℂ) * ↑ξ * I) :=
    IsConditionallyPositiveDefinite.imaginary_additive (AddMonoidHom.id ℝ) _
  have key : (fun ξ => levyCompensatedIntegrand ξ x)
      = fun ξ : ℝ => (Complex.exp ((x : ℂ) * ↑ξ * I) - 1)
          + ((if |x| < 1 then -x else 0 : ℝ) : ℂ) * ↑ξ * I := by
    funext ξ
    simp only [levyCompensatedIntegrand_def]
    by_cases hx : |x| < 1
    · simp only [ite_eq_left hx]; push_cast; ring
    · simp only [ite_eq_right hx]; push_cast; ring
  rw [key]
  exact hexp.add hlin

/-! ### Integral-level properties of the compensated integrand

The pointwise facts about `levyCompensatedIntegrand` lift to its integral against a Lévy
measure `ν`: conditional positive definiteness, continuity in the frequency variable, and
Hermitian symmetry. These feed the converse Lévy–Khintchine construction. -/

/-- The compensated integrand is continuous in the frequency variable `ξ`. -/
theorem continuous_levyCompensatedIntegrand_fst (x : ℝ) :
    Continuous (fun ξ => levyCompensatedIntegrand ξ x) := by
  unfold levyCompensatedIntegrand
  by_cases hx : |x| < 1
  · simp only [ite_eq_left hx, mul_one]; fun_prop
  · simp only [ite_eq_right hx, mul_zero, sub_zero]; fun_prop

/-- The integral of the compensated integrand against a Lévy measure is conditionally
positive definite in the frequency variable. -/
theorem cpd_integral_levyCompensatedIntegrand {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν) :
    IsConditionallyPositiveDefinite (fun ξ => ∫ x, levyCompensatedIntegrand ξ x ∂ν) := by
  intro n ξ c hc
  -- Each `conj (c i) · c j · f(ξᵢ - ξⱼ, ·)` is integrable against `ν`.
  have hint : ∀ i j : Fin n,
      Integrable (fun x => starRingEnd ℂ (c i) * c j *
        levyCompensatedIntegrand (ξ i - ξ j) x) ν :=
    fun i j => (integrable_levyCompensatedIntegrand hν _).const_mul _
  have hG_int : Integrable (fun x => ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      levyCompensatedIntegrand (ξ i - ξ j) x) ν :=
    integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => hint i j
  -- Pull the finite double sum through the integral (no Fubini).
  have key : (∫ x, ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      levyCompensatedIntegrand (ξ i - ξ j) x ∂ν) =
      ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        ∫ x, levyCompensatedIntegrand (ξ i - ξ j) x ∂ν := by
    rw [integral_finsetSum Finset.univ
      fun i _ => integrable_finsetSum Finset.univ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum Finset.univ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact integral_const_mul _ _
  have hRe : 0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      ∫ x, levyCompensatedIntegrand (ξ i - ξ j) x ∂ν).re := by
    rw [← key, show (∫ x, ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      levyCompensatedIntegrand (ξ i - ξ j) x ∂ν).re =
      ∫ x, (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        levyCompensatedIntegrand (ξ i - ξ j) x).re ∂ν from
    ((@RCLike.reCLM ℂ _).integral_comp_comm hG_int).symm]
    refine integral_nonneg fun x => ?_
    exact IsConditionallyPositiveDefinite.re_nonneg
      (cpd_levyCompensatedIntegrand_fixed x) n ξ c hc
  have hIm : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      ∫ x, levyCompensatedIntegrand (ξ i - ξ j) x ∂ν).im = 0 := by
    rw [← key]
    rw [show (∫ x, ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        levyCompensatedIntegrand (ξ i - ξ j) x ∂ν).im =
        ∫ x, (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
          levyCompensatedIntegrand (ξ i - ξ j) x).im ∂ν from
        ((@RCLike.imCLM ℂ _).integral_comp_comm hG_int).symm]
    have hpoint : ∀ x, (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        levyCompensatedIntegrand (ξ i - ξ j) x).im = 0 := by
      intro x
      exact (Complex.nonneg_iff.mp
        (cpd_levyCompensatedIntegrand_fixed x n ξ c hc)).2.symm
    have hfun : (fun x : ℝ => (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        levyCompensatedIntegrand (ξ i - ξ j) x).im) = fun _ => (0 : ℝ) :=
      funext hpoint
    rw [hfun, integral_zero]
  rw [Complex.nonneg_iff]
  exact ⟨hRe, hIm.symm⟩

/-- The integral of the compensated integrand against a Lévy measure is continuous in the
frequency variable. -/
theorem continuous_integral_levyCompensatedIntegrand
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν) :
    Continuous (fun ξ => ∫ x, levyCompensatedIntegrand ξ x ∂ν) := by
  rw [continuous_iff_continuousAt]
  intro ξ₀
  -- Dominate near `ξ₀` by `(2 + 3(|ξ₀|+1)²)·min(1, x²)`; the global bound `(2 + 3ξ²)`
  -- grows in `ξ`, so we work at each point.
  refine continuousAt_of_dominated
    (bound := fun x => (2 + 3 * (|ξ₀| + 1) ^ 2) * min 1 (x ^ 2))
    (Eventually.of_forall fun ξ => (measurable_levyCompensatedIntegrand ξ).aestronglyMeasurable)
    ?_ (hν.integrable_min_one_sq.const_mul _)
    (Eventually.of_forall fun x => (continuous_levyCompensatedIntegrand_fst x).continuousAt)
  have hev : ∀ᶠ ξ in 𝓝 ξ₀, |ξ| < |ξ₀| + 1 :=
    continuous_abs.continuousAt.eventually_lt continuousAt_const (by linarith)
  filter_upwards [hev] with ξ hξ
  filter_upwards with x
  have hξ2 : ξ ^ 2 ≤ (|ξ₀| + 1) ^ 2 := by
    nlinarith [sq_abs ξ, hξ.le, abs_nonneg ξ, abs_nonneg ξ₀]
  have hmin : (0 : ℝ) ≤ min 1 (x ^ 2) := le_min zero_le_one (sq_nonneg x)
  calc ‖levyCompensatedIntegrand ξ x‖
      ≤ (2 + 3 * ξ ^ 2) * min 1 (x ^ 2) := norm_levyCompensatedIntegrand_le ξ x
    _ ≤ (2 + 3 * (|ξ₀| + 1) ^ 2) * min 1 (x ^ 2) := by nlinarith [hξ2, hmin]

/-- Hermitian symmetry of the compensated integral: reflecting the frequency conjugates the
integral, `∫ f(-ξ, x) ∂ν = conj (∫ f(ξ, x) ∂ν)`. -/
theorem hermitian_integral_levyCompensatedIntegrand {ν : Measure ℝ} (ξ : ℝ) :
    ∫ x, levyCompensatedIntegrand (-ξ) x ∂ν =
      starRingEnd ℂ (∫ x, levyCompensatedIntegrand ξ x ∂ν) :=
  calc ∫ x, levyCompensatedIntegrand (-ξ) x ∂ν
      = ∫ x, starRingEnd ℂ (levyCompensatedIntegrand ξ x) ∂ν :=
        integral_congr_ae (ae_of_all ν fun x => (conj_levyCompensatedIntegrand ξ x).symm)
    _ = starRingEnd ℂ (∫ x, levyCompensatedIntegrand ξ x ∂ν) := integral_conj

end ProbabilityTheory

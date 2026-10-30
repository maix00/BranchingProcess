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
import all Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Lemmas.Representation.LargeJumpIdentification
import all Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Lemmas.Representation.Lemmas.AtomFreeRadii
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Small-jump identification in the Lévy–Khintchine proof

## Internal proof declarations

`scaled_smallBall_compensated_tendsto` identifies the limit of the compensated characteristic
exponent on `{x | |x| < r}` with its quadratic term. Cubic Taylor remainder and truncation
estimates provide this step for the final exponent assembly.
-/

section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder

namespace ProbabilityTheory

namespace ConvolutionSemigroup

variable (S : ConvolutionSemigroup)

/-! ### Phase 4b — Small-jump identification (cubic-remainder / δ-truncation)

The "small jump" analogue of `scaled_largeJumpSet_charFun_tendsto`. The third-order Taylor
remainder `R ξ x = exp(ixξ) − 1 − ixξ + (ixξ)²/2` is `O(|x|³)` near `0`, so the scaled
inner-ball contribution is controlled uniformly by the second moment. The band is handled
by `scaled_band_integral_tendsto` (via the Re/Im split), and the `ν`-tail vanishes as the
inner radius shrinks. -/

/-- The cubic Taylor remainder `R ξ x = exp(ixξ) − 1 − ixξ + (ixξ)²/2` is continuous in `x`. -/
private lemma smallBall_remainder_continuous (ξ : ℝ) :
    Continuous (fun x : ℝ =>
      exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) := by
  have h1 : Continuous (fun x : ℝ => (↑x : ℂ) * ↑ξ * I) :=
    (Complex.continuous_ofReal.mul continuous_const).mul continuous_const
  have h2 : Continuous (fun x : ℝ => ((↑x : ℂ) * ↑ξ) ^ 2 / 2) :=
    (((Complex.continuous_ofReal.mul continuous_const).pow 2)).div_const 2
  exact (((Complex.continuous_exp.comp h1).sub continuous_const).sub h1).add h2

/-- **Crude bound on the cubic remainder on the unit ball.** For `|x| ≤ 1`,
`‖R ξ x‖ ≤ 2 + |ξ| + ξ²/2`. (Triangle inequality; `‖exp(ixξ)‖ = 1`.) -/
private lemma smallBall_remainder_norm_le_crude {ξ x : ℝ} (hx : |x| ≤ 1) :
    ‖exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2‖ ≤
      2 + |ξ| + ξ ^ 2 / 2 := by
  have harg : (↑x : ℂ) * ↑ξ * I = (↑(x * ξ) : ℂ) * I := by push_cast; ring
  have hexp_norm : ‖exp ((↑x : ℂ) * ↑ξ * I)‖ = 1 := by
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  have hxξ : ‖(↑x : ℂ) * ↑ξ * I‖ = |x| * |ξ| := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
  have hsq : ‖((↑x : ℂ) * ↑ξ) ^ 2 / 2‖ = (|x| * |ξ|) ^ 2 / 2 := by
    rw [norm_div, norm_pow, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    norm_num
  calc ‖exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2‖
      ≤ ‖exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I‖ + ‖((↑x : ℂ) * ↑ξ) ^ 2 / 2‖ :=
        norm_add_le _ _
    _ ≤ (‖exp ((↑x : ℂ) * ↑ξ * I) - 1‖ + ‖(↑x : ℂ) * ↑ξ * I‖) + ‖((↑x : ℂ) * ↑ξ) ^ 2 / 2‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ ((‖exp ((↑x : ℂ) * ↑ξ * I)‖ + ‖(1 : ℂ)‖) + ‖(↑x : ℂ) * ↑ξ * I‖) +
          ‖((↑x : ℂ) * ↑ξ) ^ 2 / 2‖ := by gcongr; exact norm_sub_le _ _
    _ = 2 + |x| * |ξ| + (|x| * |ξ|) ^ 2 / 2 := by
        rw [hexp_norm, hxξ, hsq, norm_one]; ring
    _ ≤ 2 + |ξ| + ξ ^ 2 / 2 := by
        have hxξ_le : |x| * |ξ| ≤ |ξ| := by
          calc |x| * |ξ| ≤ 1 * |ξ| := by gcongr
            _ = |ξ| := one_mul _
        have hsq_le : (|x| * |ξ|) ^ 2 / 2 ≤ ξ ^ 2 / 2 := by
          have hnn : (0 : ℝ) ≤ |x| * |ξ| := by positivity
          have : (|x| * |ξ|) ^ 2 ≤ |ξ| ^ 2 := by gcongr
          rw [sq_abs] at this; linarith
        linarith

/- The following estimate is the `n = 3` case of `Complex.exp_bound`, specialized to the
imaginary axis. It is kept private because this exact constant and specialization only serve
the cubic remainder in this module. -/
private lemma norm_exp_I_mul_real_sub_taylor3_le {z : ℝ} (hz : |z| ≤ 1) :
    ‖Complex.exp ((↑z : ℂ) * I) - 1 - (↑z : ℂ) * I + (↑z : ℂ) ^ 2 / 2‖ ≤
      (2 / 9 : ℝ) * |z| ^ 3 := by
  set w : ℂ := (↑z : ℂ) * I with hw_def
  have hw_norm : ‖w‖ ≤ 1 := by
    rw [hw_def, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hz
  have hbound := Complex.exp_bound hw_norm (n := 3) (by decide)
  have hsum : ∑ m ∈ Finset.range 3, w ^ m / (m.factorial : ℂ) = 1 + w + w ^ 2 / 2 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one]
    simp [Nat.factorial]
  rw [hsum] at hbound
  have hw_sq : w ^ 2 = -((↑z : ℂ) ^ 2) := by
    rw [hw_def, mul_pow, Complex.I_sq]
    ring
  have hLHS : ‖Complex.exp w - (1 + w + w ^ 2 / 2)‖ =
      ‖Complex.exp w - 1 - w + (↑z : ℂ) ^ 2 / 2‖ := by
    congr 1
    rw [hw_sq]
    ring
  rw [hLHS] at hbound
  have hw_pow : ‖w‖ ^ 3 = |z| ^ 3 := by
    rw [hw_def, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  calc ‖Complex.exp w - 1 - w + (↑z : ℂ) ^ 2 / 2‖
      ≤ ‖w‖ ^ 3 * ((Nat.succ 3 : ℝ) * ((3 : ℕ).factorial * 3 : ℝ)⁻¹) := hbound
    _ = |z| ^ 3 * (4 / 18) := by rw [hw_pow]; norm_num [Nat.factorial]
    _ = (2 / 9 : ℝ) * |z| ^ 3 := by ring

/-- **Cubic bound on the remainder.** For `|x·ξ| ≤ 1`, `‖R ξ x‖ ≤ (2/9)|ξ|³|x|³`. -/
private lemma smallBall_remainder_norm_le_cube {ξ x : ℝ} (hxξ : |x * ξ| ≤ 1) :
    ‖exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2‖ ≤
      (2 / 9 : ℝ) * |ξ| ^ 3 * |x| ^ 3 := by
  have h := norm_exp_I_mul_real_sub_taylor3_le (z := x * ξ) hxξ
  have heq : exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2 =
      Complex.exp ((↑(x * ξ) : ℂ) * I) - 1 - (↑(x * ξ) : ℂ) * I + (↑(x * ξ) : ℂ) ^ 2 / 2 := by
    push_cast; ring
  rw [heq]
  refine h.trans (le_of_eq ?_)
  rw [abs_mul, mul_pow]; ring

/-- The clamped cubic remainder `Rc ξ r x := R ξ (clamp_{[-r,r]} x)` is continuous and, for
`r ≤ 1`, globally bounded by `2 + |ξ| + ξ²/2`. Clamping makes the otherwise-quadratic
remainder integrable on the whole line. -/
private lemma remainder_clamp_continuous (r : ℝ) (ξ : ℝ) :
    Continuous (fun x : ℝ =>
      (fun y : ℝ => exp ((↑y : ℂ) * ↑ξ * I) - 1 - (↑y : ℂ) * ↑ξ * I + ((↑y : ℂ) * ↑ξ) ^ 2 / 2)
        (max (-r) (min x r))) :=
  (smallBall_remainder_continuous ξ).comp
    (continuous_const.max (continuous_id.min continuous_const))

/-- On the ball `{|x| < r}` (with `r ≤ 1`) the clamp is inactive: `clamp x = x`. -/
private lemma clamp_eq_of_abs_lt {r x : ℝ} (hx : |x| < r) : max (-r) (min x r) = x := by
  obtain ⟨hxl, hxr⟩ := abs_lt.mp hx
  rw [min_eq_left (le_of_lt hxr), max_eq_right (le_of_lt hxl)]

private lemma remainder_clamp_norm_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ξ x : ℝ) :
    ‖(fun y : ℝ => exp ((↑y : ℂ) * ↑ξ * I) - 1 - (↑y : ℂ) * ↑ξ * I + ((↑y : ℂ) * ↑ξ) ^ 2 / 2)
        (max (-r) (min x r))‖ ≤ 2 + |ξ| + ξ ^ 2 / 2 := by
  have hc : |max (-r) (min x r)| ≤ 1 := by
    have h1 : max (-r) (min x r) ≤ r := max_le (by linarith) (min_le_right _ _)
    have h2 : -r ≤ max (-r) (min x r) := le_max_left _ _
    rw [abs_le]; exact ⟨by linarith, by linarith⟩
  exact smallBall_remainder_norm_le_crude hc

/-- The cubic Taylor remainder is integrable on the ball `{|x| < r}` (for `r ≤ 1`) under any
finite measure: clamp to `[-r, r]` to obtain a globally bounded continuous function that
agrees with the remainder on the ball. -/
private lemma remainder_integrableOn_ball
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ξ : ℝ) (m : Measure ℝ) [IsFiniteMeasure m] :
    IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
      {x : ℝ | |x| < r} m := by
  have hmeas : MeasurableSet {x : ℝ | |x| < r} :=
    (isOpen_lt continuous_abs continuous_const).measurableSet
  have hclamp_int : IntegrableOn
      (fun x : ℝ =>
        (fun y : ℝ =>
          exp ((↑y : ℂ) * ↑ξ * I) - 1 - (↑y : ℂ) * ↑ξ * I + ((↑y : ℂ) * ↑ξ) ^ 2 / 2)
          (max (-r) (min x r)))
      {x : ℝ | |x| < r} m :=
    Measure.integrableOn_of_bounded (measure_ne_top _ _)
      (remainder_clamp_continuous r ξ).aestronglyMeasurable
      (M := 2 + |ξ| + ξ ^ 2 / 2)
      (Filter.Eventually.of_forall (remainder_clamp_norm_le hr0 hr1 ξ))
  refine hclamp_int.congr_fun (fun x hx => ?_) hmeas
  show (fun y : ℝ =>
      exp ((↑y : ℂ) * ↑ξ * I) - 1 - (↑y : ℂ) * ↑ξ * I + ((↑y : ℂ) * ↑ξ) ^ 2 / 2)
      (max (-r) (min x r)) = _
  rw [clamp_eq_of_abs_lt hx]

/-- **Band convergence for the complex cubic remainder.** For atom-free radii `0 < δ < r`,
the scaled band integral of the cubic remainder `R ξ x` converges to its `ν`-band integral.
Re/Im split (à la `scaled_largeJumpSet_charFun_tendsto`), feeding the *clamped* real/imaginary
parts to `scaled_band_integral_tendsto`. -/
private lemma remainder_band_tendsto
    {δ r : ℝ} (hδ : 0 < δ) (hδr : δ < r) (hr1 : r ≤ 1) (ξ : ℝ)
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν)
    (hν_δ : ν {x | |x| = δ} = 0) (hν_r : ν {x | |x| = r} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun k => ((t_seq k).val⁻¹ : ℂ) *
        ∫ x in {x | δ ≤ |x| ∧ |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
          ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in {x | δ ≤ |x| ∧ |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν)) := by
  have hr0 : (0 : ℝ) ≤ r := le_of_lt (hδ.trans hδr)
  set R : ℝ → ℂ := fun x =>
    exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2 with hR_def
  -- Clamped real and imaginary parts, globally bounded by `M := 2 + |ξ| + ξ²/2`.
  set M : ℝ := 2 + |ξ| + ξ ^ 2 / 2 with hM_def
  have hM_nn : (0 : ℝ) ≤ M := by positivity
  set Rc : ℝ → ℂ := fun x => R (max (-r) (min x r)) with hRc_def
  have hRc_cont : Continuous Rc := remainder_clamp_continuous r ξ
  have hRc_bnd : ∀ x, ‖Rc x‖ ≤ M := remainder_clamp_norm_le hr0 hr1 ξ
  set gRe : ℝ → ℝ := fun x => (Rc x).re with hgRe_def
  set gIm : ℝ → ℝ := fun x => (Rc x).im with hgIm_def
  have hgRe_cont : Continuous gRe := Complex.continuous_re.comp hRc_cont
  have hgIm_cont : Continuous gIm := Complex.continuous_im.comp hRc_cont
  have hgRe_bnd : ∀ x, |gRe x| ≤ M := fun x =>
    (abs_re_le_norm (Rc x)).trans (hRc_bnd x)
  have hgIm_bnd : ∀ x, |gIm x| ≤ M := fun x =>
    (abs_im_le_norm (Rc x)).trans (hRc_bnd x)
  -- The band, measurable and contained in the ball.
  set band : Set ℝ := {x | δ ≤ |x| ∧ |x| < r} with hband_def
  have h_meas_band : MeasurableSet band :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  -- On the band, `Rc = R` (the clamp is inactive since `|x| < r`).
  have hRc_eq : ∀ x ∈ band, Rc x = R x := fun x hx => by
    show R (max (-r) (min x r)) = R x
    rw [clamp_eq_of_abs_lt hx.2]
  -- The band has finite `ν`-mass (it avoids a neighbourhood of `0`).
  have hν_band : ν band < ⊤ :=
    lt_of_le_of_lt (measure_mono (fun x hx => hx.1)) (hν.measure_setOf_abs_ge_lt_top hδ)
  -- Decomposition of the complex band integral via Re/Im of `Rc`, for any measure finite on the band.
  have h_decomp : ∀ (m : Measure ℝ), m band < ⊤ →
      ∫ x in band, R x ∂m =
        (↑(∫ x in band, gRe x ∂m) : ℂ) + (↑(∫ x in band, gIm x ∂m) : ℂ) * I := by
    intro m hm
    have hR_int : IntegrableOn R band m := by
      have : IntegrableOn Rc band m :=
        Measure.integrableOn_of_bounded hm.ne hRc_cont.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun x => by
            simpa [Real.norm_eq_abs] using hRc_bnd x))
      exact this.congr_fun hRc_eq h_meas_band
    have h := setIntegral_re_add_im hR_int
    simp only [RCLike.I_to_complex] at h
    have hRe_int : ∫ x in band, RCLike.re (R x) ∂m = ∫ x in band, gRe x ∂m :=
      setIntegral_congr_fun h_meas_band (fun x hx => by
        simp only [hgRe_def, RCLike.re_to_complex, hRc_eq x hx])
    have hIm_int : ∫ x in band, RCLike.im (R x) ∂m = ∫ x in band, gIm x ∂m :=
      setIntegral_congr_fun h_meas_band (fun x hx => by
        simp only [hgIm_def, RCLike.im_to_complex, hRc_eq x hx])
    rw [hRe_int, hIm_int] at h
    exact h.symm
  -- Scalar band limits for `gRe`, `gIm`.
  have h_re_lim : Tendsto (fun k => (t_seq k).val⁻¹ *
      ∫ x in band, gRe x ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in band, gRe x ∂ν)) :=
    S.scaled_band_integral_tendsto hδ hδr gRe hgRe_cont hM_nn hgRe_bnd
      hν hν_δ hν_r h_jump
  have h_im_lim : Tendsto (fun k => (t_seq k).val⁻¹ *
      ∫ x in band, gIm x ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in band, gIm x ∂ν)) :=
    S.scaled_band_integral_tendsto hδ hδr gIm hgIm_cont hM_nn hgIm_bnd
      hν hν_δ hν_r h_jump
  -- Recombine into the complex limit.
  have h_re_lim_C : Tendsto (fun k => (↑((t_seq k).val⁻¹ *
      ∫ x in band, gRe x ∂(S.measure (t_seq k) : Measure ℝ)) : ℂ))
      atTop (𝓝 (↑(∫ x in band, gRe x ∂ν) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp h_re_lim
  have h_im_lim_C : Tendsto (fun k => (↑((t_seq k).val⁻¹ *
      ∫ x in band, gIm x ∂(S.measure (t_seq k) : Measure ℝ)) : ℂ) * I)
      atTop (𝓝 ((↑(∫ x in band, gIm x ∂ν) : ℂ) * I)) :=
    ((Complex.continuous_ofReal.tendsto _).comp h_im_lim).mul_const I
  have h_sum := h_re_lim_C.add h_im_lim_C
  rw [← h_decomp ν hν_band] at h_sum
  refine h_sum.congr (fun k => ?_)
  rw [h_decomp (S.measure (t_seq k) : Measure ℝ) (measure_lt_top _ _)]
  push_cast
  ring

/-- `x²` is integrable on the ball `{|x| < r}` under any finite measure: on the ball
`x² = min (x²) (r²)`, the latter being globally bounded and continuous. -/
private lemma sq_integrableOn_ball
    (r : ℝ) (m : Measure ℝ) [IsFiniteMeasure m] :
    IntegrableOn (fun x : ℝ => x ^ 2) {x : ℝ | |x| < r} m := by
  have hmeas : MeasurableSet {x : ℝ | |x| < r} :=
    (isOpen_lt continuous_abs continuous_const).measurableSet
  have hg_int : IntegrableOn (fun x : ℝ => min (x ^ 2) (r ^ 2)) {x : ℝ | |x| < r} m := by
    refine Measure.integrableOn_of_bounded (measure_ne_top _ _)
      (((continuous_pow 2).min continuous_const).aestronglyMeasurable)
      (M := r ^ 2) (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs]
    rw [abs_le]
    constructor
    · have : (0 : ℝ) ≤ min (x ^ 2) (r ^ 2) := le_min (sq_nonneg x) (sq_nonneg r)
      linarith [sq_nonneg r]
    · exact min_le_right _ _
  refine hg_int.congr_fun (fun x hx => ?_) hmeas
  have hx' : |x| < r := hx
  have : x ^ 2 ≤ r ^ 2 := by rw [← sq_abs x]; gcongr
  exact min_eq_left this

/-- **Inner-ball cube estimate.** For `0 < δ ≤ 1` with `δ·|ξ| ≤ 1`, the scaled inner-ball
integral of the cubic remainder is dominated by the inner-ball second moment:
`‖∫_{|x|<δ} R dm‖ ≤ (2/9)|ξ|³·δ·∫_{|x|<δ} x² dm`. (Cube bound `‖R x‖ ≤ (2/9)|ξ|³|x|³`,
then `|x|³ ≤ δ·x²` on the ball.) -/
private lemma remainder_inner_ball_norm_le
    {δ : ℝ} (_hδ : 0 < δ) (_hδ1 : δ ≤ 1) (ξ : ℝ) (hδξ : δ * |ξ| ≤ 1)
    (m : Measure ℝ)
    (hRint : IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
      {x : ℝ | |x| < δ} m)
    (hsqint : IntegrableOn (fun x : ℝ => x ^ 2) {x : ℝ | |x| < δ} m) :
    ‖∫ x in {x | |x| < δ},
        (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂m‖ ≤
      (2 / 9 : ℝ) * |ξ| ^ 3 * δ * ∫ x in {x | |x| < δ}, x ^ 2 ∂m := by
  have hmeas : MeasurableSet {x : ℝ | |x| < δ} :=
    (isOpen_lt continuous_abs continuous_const).measurableSet
  -- Cube bound holds on the ball: for `|x| < δ`, `|x·ξ| ≤ δ·|ξ| ≤ 1`.
  have hcube : ∀ x ∈ {x : ℝ | |x| < δ},
      ‖exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2‖ ≤
        (2 / 9 : ℝ) * |ξ| ^ 3 * |x| ^ 3 := by
    intro x hx
    refine smallBall_remainder_norm_le_cube ?_
    calc |x * ξ| = |x| * |ξ| := abs_mul x ξ
      _ ≤ δ * |ξ| := by gcongr; exact le_of_lt hx
      _ ≤ 1 := hδξ
  -- Step 1: `‖∫ R‖ ≤ ∫ ‖R‖`.
  have h1 : ‖∫ x in {x | |x| < δ},
      (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂m‖ ≤
      ∫ x in {x | |x| < δ},
        ‖exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2‖ ∂m :=
    norm_integral_le_integral_norm _
  -- Integrability of `‖R‖` on the ball (`R` integrable ⟹ `‖R‖` integrable).
  have hR_int : IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
      {x : ℝ | |x| < δ} m := hRint
  -- The dominating bound `(2/9)|ξ|³·δ·x²` is integrable on the ball.
  have hbound_int : IntegrableOn (fun x : ℝ => (2 / 9 : ℝ) * |ξ| ^ 3 * δ * x ^ 2)
      {x : ℝ | |x| < δ} m :=
    hsqint.const_mul ((2 / 9 : ℝ) * |ξ| ^ 3 * δ)
  -- Step 2: monotone comparison `∫ ‖R‖ ≤ ∫ (2/9)|ξ|³·δ·x²`.
  have hnorm_int : IntegrableOn (fun x : ℝ =>
      ‖exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2‖)
      {x : ℝ | |x| < δ} m := hR_int.norm
  have h2 : ∫ x in {x | |x| < δ},
      ‖exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2‖ ∂m ≤
      ∫ x in {x | |x| < δ}, (2 / 9 : ℝ) * |ξ| ^ 3 * δ * x ^ 2 ∂m := by
    refine setIntegral_mono_on hnorm_int hbound_int hmeas (fun x hx => ?_)
    calc ‖exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2‖
        ≤ (2 / 9 : ℝ) * |ξ| ^ 3 * |x| ^ 3 := hcube x hx
      _ ≤ (2 / 9 : ℝ) * |ξ| ^ 3 * δ * x ^ 2 := by
          have hx' : |x| < δ := hx
          have hcube_le : |x| ^ 3 ≤ δ * x ^ 2 := by
            have heq : |x| ^ 3 = |x| * x ^ 2 := by rw [← sq_abs x]; ring
            rw [heq]
            gcongr
          calc (2 / 9 : ℝ) * |ξ| ^ 3 * |x| ^ 3
              ≤ (2 / 9 : ℝ) * |ξ| ^ 3 * (δ * x ^ 2) := by gcongr
            _ = (2 / 9 : ℝ) * |ξ| ^ 3 * δ * x ^ 2 := by ring
  -- Pull the constant out of the dominating integral.
  have h3 : ∫ x in {x | |x| < δ}, (2 / 9 : ℝ) * |ξ| ^ 3 * δ * x ^ 2 ∂m =
      (2 / 9 : ℝ) * |ξ| ^ 3 * δ * ∫ x in {x | |x| < δ}, x ^ 2 ∂m := by
    rw [← integral_const_mul]
  calc ‖∫ x in {x | |x| < δ},
        (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂m‖
      ≤ ∫ x in {x | |x| < δ},
          ‖exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2‖ ∂m := h1
    _ ≤ ∫ x in {x | |x| < δ}, (2 / 9 : ℝ) * |ξ| ^ 3 * δ * x ^ 2 ∂m := h2
    _ = (2 / 9 : ℝ) * |ξ| ^ 3 * δ * ∫ x in {x | |x| < δ}, x ^ 2 ∂m := h3

/-- **Ball = inner-ball ⊎ band split for the cubic remainder.** For `0 < δ < r ≤ 1` and any
finite measure, the remainder integral over the ball `{|x| < r}` is the sum of the inner-ball
integral and the band integral. -/
private lemma remainder_ball_split
    {δ r : ℝ} (_hδ : 0 < δ) (hδr : δ < r) (_hr1 : r ≤ 1) (ξ : ℝ)
    (m : Measure ℝ)
    (hRint : IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
      {x : ℝ | |x| < r} m) :
    ∫ x in {x | |x| < r},
        (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂m =
      (∫ x in {x | |x| < δ},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂m) +
      ∫ x in {x | δ ≤ |x| ∧ |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂m := by
  set R : ℝ → ℂ := fun x =>
    exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2 with hR_def
  have h_inner_sub : {x : ℝ | |x| < δ} ⊆ {x : ℝ | |x| < r} := fun x hx => lt_trans hx hδr
  have h_band_sub : {x : ℝ | δ ≤ |x| ∧ |x| < r} ⊆ {x : ℝ | |x| < r} := fun x hx => hx.2
  have hR_int_ball : IntegrableOn R {x : ℝ | |x| < r} m := hRint
  have hR_int_inner : IntegrableOn R {x : ℝ | |x| < δ} m :=
    hR_int_ball.mono_set h_inner_sub
  have hR_int_band : IntegrableOn R {x : ℝ | δ ≤ |x| ∧ |x| < r} m :=
    hR_int_ball.mono_set h_band_sub
  have h_disj : Disjoint {x : ℝ | |x| < δ} {x : ℝ | δ ≤ |x| ∧ |x| < r} := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx'.1 (not_le.mpr hx)
  have h_union : {x : ℝ | |x| < r} = {x : ℝ | |x| < δ} ∪ {x : ℝ | δ ≤ |x| ∧ |x| < r} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro hx
      rcases lt_or_ge (|x|) δ with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hx⟩
    · rintro (h | ⟨_, h⟩)
      · exact lt_trans h hδr
      · exact h
  have h_meas_band : MeasurableSet {x : ℝ | δ ≤ |x| ∧ |x| < r} :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  rw [h_union, setIntegral_union h_disj h_meas_band hR_int_inner hR_int_band]

/-- The scaled small-ball integral of the cubic remainder converges to the `ν`-integral.
δ-truncation: inner ball `O(δ)` by the Taylor bound + uniform second moment; band by
`scaled_band_integral_tendsto` (Re/Im); ν-tail by dominated convergence as `δ → 0`. -/
private lemma scaled_smallBall_remainder_tendsto
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (ξ : ℝ)
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν)
    (hν_r : ν {x | |x| = r} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (hσ_bdd : ∃ C : ℝ, ∀ k, (t_seq k).val⁻¹ *
        ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ) ≤ C)
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun k => ((t_seq k).val⁻¹ : ℂ) *
        ∫ x in {x | |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
          ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in {x | |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν)) := by
  -- `ξ = 0`: the remainder is identically `0`; both sides vanish.
  rcases eq_or_ne ξ 0 with hξ0 | hξ0
  · subst hξ0
    have hint0 : ∀ (m : Measure ℝ),
        ∫ x in {x : ℝ | |x| < r},
          (exp ((↑x : ℂ) * ↑(0:ℝ) * I) - 1 - (↑x : ℂ) * ↑(0:ℝ) * I
            + ((↑x : ℂ) * ↑(0:ℝ)) ^ 2 / 2) ∂m = 0 := by
      intro m
      have : (fun x : ℝ => exp ((↑x : ℂ) * ↑(0:ℝ) * I) - 1 - (↑x : ℂ) * ↑(0:ℝ) * I
            + ((↑x : ℂ) * ↑(0:ℝ)) ^ 2 / 2) = fun _ : ℝ => (0 : ℂ) := by
        funext x; simp
      simp only [this, integral_zero]
    simp only [hint0, mul_zero]
    exact tendsto_const_nhds
  -- `ξ ≠ 0`: δ-truncation with an atom-free shrinking sequence inside `(0, min r (1/|ξ|))`.
  obtain ⟨C, hC⟩ := hσ_bdd
  have hξ_pos : 0 < |ξ| := abs_pos.mpr hξ0
  have hc_pos : 0 < min r (1 / |ξ|) := lt_min hr (by positivity)
  obtain ⟨δ, hδ_pos, hδ_lt, hδ_atom, hδ_lim⟩ := hν.exists_atomFree_seq_tendsto_zero hc_pos
  -- For each `m`: `δ m < r`, `δ m ≤ 1`, `δ m·|ξ| ≤ 1`.
  have hδ_ltr : ∀ m, δ m < r := fun m => (hδ_lt m).trans_le (min_le_left _ _)
  have hδ_le1 : ∀ m, δ m ≤ 1 := fun m => le_of_lt ((hδ_ltr m).trans_le hr1)
  have hδξ : ∀ m, δ m * |ξ| ≤ 1 := fun m => by
    have h := (hδ_lt m).trans_le (min_le_right _ _)
    rw [lt_div_iff₀ hξ_pos] at h
    exact le_of_lt h
  -- The (finite) `ν`-second moment on the ball, used as the `ν`-inner-ball constant.
  set Bν : ℝ := ∫ x in {x | |x| < r}, x ^ 2 ∂ν with hBν_def
  -- Inner-ball `ν`-second moment is bounded by `Bν`.
  have hν_inner_sq_le : ∀ m, ∫ x in {x | |x| < δ m}, x ^ 2 ∂ν ≤ Bν := by
    intro m
    refine setIntegral_mono_set (sq_integrableOn_ball_levy hν r)
      (ae_restrict_of_forall_mem
        ((isOpen_lt continuous_abs continuous_const).measurableSet) (fun x _ => sq_nonneg x))
      (LE.le.eventuallyLE (fun x hx => lt_trans hx (hδ_ltr m)))
  -- Use the `Metric` characterisation of convergence in `ℂ`.
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Pick `m` so the two inner-ball contributions each drop below `ε/3`.
  -- `(2/9)|ξ|³·δ m·C → 0` and `(2/9)|ξ|³·δ m·Bν → 0`.
  have htendC : Tendsto (fun m => (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * C) atTop (𝓝 0) := by
    have : Tendsto (fun m => (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * C) atTop
        (𝓝 ((2 / 9 : ℝ) * |ξ| ^ 3 * 0 * C)) := by
      exact ((tendsto_const_nhds.mul hδ_lim).mul tendsto_const_nhds)
    simpa using this
  have htendBν : Tendsto (fun m => (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * Bν) atTop (𝓝 0) := by
    have : Tendsto (fun m => (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * Bν) atTop
        (𝓝 ((2 / 9 : ℝ) * |ξ| ^ 3 * 0 * Bν)) := by
      exact ((tendsto_const_nhds.mul hδ_lim).mul tendsto_const_nhds)
    simpa using this
  have hevC : ∀ᶠ m in atTop, (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * C < ε / 3 :=
    htendC.eventually_lt_const (by linarith)
  have hevBν : ∀ᶠ m in atTop, (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * Bν < ε / 3 :=
    htendBν.eventually_lt_const (by linarith)
  obtain ⟨m, hmC, hmBν⟩ := (hevC.and hevBν).exists
  -- Band limit for this `m` ⟹ an index `N` controlling the band term.
  have h_band_lim := S.remainder_band_tendsto (hδ_pos m) (hδ_ltr m) hr1 ξ
    hν (hδ_atom m) hν_r h_jump
  rw [Metric.tendsto_atTop] at h_band_lim
  obtain ⟨N, hN⟩ := h_band_lim (ε / 3) (by linarith)
  refine ⟨N, fun k hk => ?_⟩
  -- Abbreviations for the four set integrals at radius `δ m`.
  set μk : Measure ℝ := (S.measure (t_seq k) : Measure ℝ) with hμk_def
  set tk : ℝ := (t_seq k).val⁻¹ with htk_def
  set ck : ℂ := ((t_seq k).val⁻¹ : ℂ) with hck_def
  have htk_pos : 0 < tk := inv_pos.mpr (t_seq k).2
  have hck_eq : ck = (↑tk : ℂ) := by rw [hck_def, htk_def]; push_cast; ring
  -- Split the ball integral (μk and ν) into inner ball + band.
  have hsplit_μ := remainder_ball_split (hδ_pos m) (hδ_ltr m) hr1 ξ μk
    (remainder_integrableOn_ball (le_of_lt hr) hr1 ξ μk)
  have hsplit_ν := remainder_ball_split (hδ_pos m) (hδ_ltr m) hr1 ξ ν
    (remainder_integrableOn_ball_levy hr1 ξ hν)
  -- Name the four set-integrals atomically (so `ring` treats them as opaque scalars).
  set iμ : ℂ := ∫ x in {x | |x| < δ m},
      (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂μk with hiμ_def
  set bμ : ℂ := ∫ x in {x | δ m ≤ |x| ∧ |x| < r},
      (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂μk with hbμ_def
  set iν : ℂ := ∫ x in {x | |x| < δ m},
      (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν with hiν_def
  set bν : ℂ := ∫ x in {x | δ m ≤ |x| ∧ |x| < r},
      (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν with hbν_def
  rw [dist_eq_norm]
  -- The ball integrals now fold to `iμ + bμ` and `iν + bν`.
  rw [hsplit_μ, hsplit_ν]
  -- Regroup and split via the triangle inequality.
  rw [show ck * (iμ + bμ) - (iν + bν) = (ck * iμ - iν) + (ck * bμ - bν) from by ring]
  refine lt_of_le_of_lt (norm_add_le _ _) ?_
  -- Band term: bounded by `ε/3` via `hN`.
  have hband_lt : ‖ck * bμ - bν‖ < ε / 3 := by
    rw [hbμ_def, hbν_def, hck_def, hμk_def]
    have hth := hN k hk
    rwa [dist_eq_norm] at hth
  -- Inner term: bounded by `ε/3 + ε/3` via the two inner-ball estimates.
  have hinner_lt : ‖ck * iμ - iν‖ < ε / 3 + ε / 3 := by
    refine lt_of_le_of_lt (norm_sub_le _ _) ?_
    -- μ-side inner ball.
    have hμ_norm : ‖ck * iμ‖ ≤ (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * C := by
      rw [hck_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htk_pos, hiμ_def]
      calc tk * ‖∫ x in {x | |x| < δ m},
            (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂μk‖
          ≤ tk * ((2 / 9 : ℝ) * |ξ| ^ 3 * δ m * ∫ x in {x | |x| < δ m}, x ^ 2 ∂μk) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt htk_pos)
            exact remainder_inner_ball_norm_le (hδ_pos m) (hδ_le1 m) ξ (hδξ m) μk
              (remainder_integrableOn_ball (le_of_lt (hδ_pos m)) (hδ_le1 m) ξ μk)
              (sq_integrableOn_ball (δ m) μk)
        _ = (2 / 9 : ℝ) * |ξ| ^ 3 * δ m *
              (tk * ∫ x in {x | |x| < δ m}, x ^ 2 ∂μk) := by ring
        _ ≤ (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * C := by
            refine mul_le_mul_of_nonneg_left ?_ (by have := hδ_pos m; positivity)
            calc tk * ∫ x in {x | |x| < δ m}, x ^ 2 ∂μk
                ≤ tk * ∫ x in {x | |x| < r}, x ^ 2 ∂μk := by
                  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt htk_pos)
                  refine setIntegral_mono_set (sq_integrableOn_ball r μk)
                    (ae_restrict_of_forall_mem
                      ((isOpen_lt continuous_abs continuous_const).measurableSet)
                      (fun x _ => sq_nonneg x))
                    (LE.le.eventuallyLE (fun x hx => lt_trans hx (hδ_ltr m)))
              _ ≤ C := hC k
    -- ν-side inner ball.
    have hν_norm : ‖iν‖ ≤ (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * Bν := by
      rw [hiν_def]
      calc ‖∫ x in {x | |x| < δ m},
            (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν‖
          ≤ (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * ∫ x in {x | |x| < δ m}, x ^ 2 ∂ν :=
            remainder_inner_ball_norm_le (hδ_pos m) (hδ_le1 m) ξ (hδξ m) ν
              (remainder_integrableOn_ball_levy (hδ_le1 m) ξ hν)
              (sq_integrableOn_ball_levy hν (δ m))
        _ ≤ (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * Bν := by
            refine mul_le_mul_of_nonneg_left (hν_inner_sq_le m) (by have := hδ_pos m; positivity)
    calc ‖ck * iμ‖ + ‖iν‖
        ≤ (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * C + (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * Bν :=
          add_le_add hμ_norm hν_norm
      _ < ε / 3 + ε / 3 := by linarith [hmC, hmBν]
  linarith [hband_lt, hinner_lt]

/-- **Small-jump identification at radius `r`.** The limit is expressed with the
*remainder* ν-integral; the conversion to `∫ (exp − 1 − ixξ) dν` happens in the final
assembly, where the `−σ_G²ξ²/2` regrouping is done once. -/
lemma scaled_smallBall_compensated_tendsto
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (ξ : ℝ)
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν)
    (hν_r : ν {x | |x| = r} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}} {σ_sq_r : ℝ}
    (hσ : Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ)) atTop (𝓝 σ_sq_r))
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun k => ((t_seq k).val⁻¹ : ℂ) *
        ∫ x in {x | |x| < r}, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I)
          ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (-(↑σ_sq_r * ↑ξ ^ 2 / 2)
          + ∫ x in {x | |x| < r},
              (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν)) := by
  -- A convergent real sequence is bounded above; supplies `hσ_bdd` for lemma 1.
  have hσ_bdd : ∃ C : ℝ, ∀ k, (t_seq k).val⁻¹ *
      ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ) ≤ C := by
    obtain ⟨C, hC⟩ := bddAbove_def.mp hσ.isBoundedUnder_le.bddAbove_range
    exact ⟨C, fun k => hC _ ⟨k, rfl⟩⟩
  -- Remainder limit from lemma 1.
  have hrem := S.scaled_smallBall_remainder_tendsto hr hr1 ξ hν hν_r hσ_bdd h_jump
  -- The quadratic-correction limit: `↑ξ²/2 · ↑(t⁻¹·∫x²dμ_k) → ↑ξ²/2 · ↑σ_sq_r`.
  have hquad : Tendsto (fun k => (↑ξ ^ 2 / 2 : ℂ) *
      (↑((t_seq k).val⁻¹ * ∫ x in {x | |x| < r}, x ^ 2
        ∂(S.measure (t_seq k) : Measure ℝ)) : ℂ))
      atTop (𝓝 ((↑ξ ^ 2 / 2 : ℂ) * (↑σ_sq_r : ℂ))) :=
    Tendsto.const_mul _ ((Complex.continuous_ofReal.tendsto _).comp hσ)
  -- Combine: each `(exp−1−ixξ)`-integral is the remainder integral minus the quadratic term.
  have hpereq : ∀ k, ((t_seq k).val⁻¹ : ℂ) *
      ∫ x in {x | |x| < r}, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I)
        ∂(S.measure (t_seq k) : Measure ℝ) =
      (((t_seq k).val⁻¹ : ℂ) * ∫ x in {x | |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
          ∂(S.measure (t_seq k) : Measure ℝ)) -
      (↑ξ ^ 2 / 2 : ℂ) * (↑((t_seq k).val⁻¹ *
          ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ)) : ℂ) := by
    intro k
    set μk : Measure ℝ := (S.measure (t_seq k) : Measure ℝ) with hμk_def
    have hmeas : MeasurableSet {x : ℝ | |x| < r} :=
      (isOpen_lt continuous_abs continuous_const).measurableSet
    -- Split the `(exp−1−ixξ)` integral into remainder minus the quadratic part.
    have hRint : IntegrableOn
        (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I
          + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) {x : ℝ | |x| < r} μk :=
      remainder_integrableOn_ball (le_of_lt hr) hr1 ξ μk
    have hQint : IntegrableOn (fun x : ℝ => ((↑x : ℂ) * ↑ξ) ^ 2 / 2) {x : ℝ | |x| < r} μk := by
      have hrw : (fun x : ℝ => ((↑x : ℂ) * ↑ξ) ^ 2 / 2) =
          fun x : ℝ => (↑((x ^ 2 * (ξ ^ 2 / 2) : ℝ)) : ℂ) := by
        funext x; push_cast; ring
      rw [hrw]
      exact (((sq_integrableOn_ball r μk).mul_const (ξ ^ 2 / 2))).ofReal
    -- `(exp−1−ixξ) = R − (xξ)²/2` pointwise.
    have hsub : ∫ x in {x | |x| < r}, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) ∂μk =
        (∫ x in {x | |x| < r},
            (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂μk) -
          ∫ x in {x | |x| < r}, ((↑x : ℂ) * ↑ξ) ^ 2 / 2 ∂μk := by
      rw [← integral_sub hRint hQint]
      refine setIntegral_congr_fun hmeas (fun x _ => ?_)
      ring
    -- The quadratic part equals `↑ξ²/2 · ↑(∫ x² dμk)`.
    have hquad_real : ∫ x in {x | |x| < r}, (ξ ^ 2 / 2 * x ^ 2 : ℝ) ∂μk =
        ξ ^ 2 / 2 * ∫ x in {x | |x| < r}, x ^ 2 ∂μk :=
      integral_const_mul (ξ ^ 2 / 2) _
    have hquad_int : ∫ x in {x | |x| < r}, ((↑x : ℂ) * ↑ξ) ^ 2 / 2 ∂μk =
        (↑ξ ^ 2 / 2 : ℂ) * (↑(∫ x in {x | |x| < r}, x ^ 2 ∂μk) : ℂ) := by
      have hcongr : ∫ x in {x | |x| < r}, ((↑x : ℂ) * ↑ξ) ^ 2 / 2 ∂μk =
          ∫ x in {x | |x| < r}, (↑((ξ ^ 2 / 2 * x ^ 2 : ℝ)) : ℂ) ∂μk := by
        refine setIntegral_congr_fun hmeas (fun x _ => ?_)
        push_cast; ring
      rw [hcongr]
      rw [show (∫ x in {x | |x| < r}, (↑((ξ ^ 2 / 2 * x ^ 2 : ℝ)) : ℂ) ∂μk) =
          (↑(∫ x in {x | |x| < r}, (ξ ^ 2 / 2 * x ^ 2 : ℝ) ∂μk) : ℂ) from integral_ofReal]
      rw [hquad_real]
      push_cast
      ring
    rw [hsub, hquad_int, mul_sub]
    rw [hμk_def]
    push_cast
    ring
  -- Take the limit of the per-`k` identity.
  have hlim := (hrem.sub hquad).congr (fun k => (hpereq k).symm)
  -- Match the stated RHS: `∫R dν − ↑ξ²/2·↑σ_sq_r = −(↑σ_sq_r·↑ξ²/2) + ∫R dν`.
  have hRHS : (∫ x in {x | |x| < r},
        (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν) -
        (↑ξ ^ 2 / 2 : ℂ) * (↑σ_sq_r : ℂ) =
      -(↑σ_sq_r * ↑ξ ^ 2 / 2)
        + ∫ x in {x | |x| < r},
            (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν := by
    ring
  rw [← hRHS]
  exact hlim

end ConvolutionSemigroup

end ProbabilityTheory

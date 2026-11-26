/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.MeasureTheory.Convergence.TailExpectation
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# First-moment convergence from lower tails and upper means

## Public declarations

* `ProbabilityTheory.tendsto_eLpNorm_one_div_sub_of_lower_tails_and_upper_mean`:
  for probability laws `μ_i`, scales `L_i→∞` and integrable real variables
  `X_i`, if `E exp(-X_i)≤exp(A L_i)`, each lower tail below `c L_i` is
  bounded by `exp(-p L_i)` for some `p>0`, and
  `limsup E[X_i/L_i]≤c`, then `‖X_i/L_i-c‖_(L¹(μ_i))→0`.
  Neither second moments nor a common sample law are required.

The finite estimate uses the existing one-sided exponential expectation
inequality applied to `min(X,z)`. Native Bochner and `L¹` seminorm identities
then give convergence. This is the first-moment step used with the endpoint
bounds of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with
Infinite Offspring* (Fudan University, 2026), Chapter 4, Theorems 1.1 and 1.2.
The statement itself is independent of branching and of logarithmic scales.
-/

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ProbabilityTheory

set_option backward.isDefEq.respectTransparency false

private lemma integral_abs_sub_le_of_exp_neg_and_lower_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) (hm : Measurable X)
    (hExp : Integrable (fun ω => Real.exp (-X ω)) μ)
    {z L p M : ℝ} (hL : 0 ≤ L)
    (hprob : μ.real {ω | X ω ≤ z} ≤ p)
    (hExpBound : (∫ ω, Real.exp (-X ω) ∂μ) ≤ M) :
    (∫ ω, |X ω - z| ∂μ) ≤ (∫ ω, X ω ∂μ) - z +
      2 * (max z 0 + L) * p + 2 * Real.exp (-L) * (M + Real.exp (-z)) := by
  let Y := fun ω => min (X ω) z
  have hY : Integrable Y μ := hX.inf (integrable_const z)
  have hYe : Integrable (fun ω => Real.exp (-Y ω)) μ := by
    have h : (fun ω => Real.exp (-Y ω)) =
        fun ω => max (Real.exp (-X ω)) (Real.exp (-z)) := by
      funext ω
      dsimp [Y]
      rcases le_total (X ω) z with h | h
      · rw [min_eq_left h, max_eq_left (Real.exp_le_exp.mpr (neg_le_neg h))]
      · rw [min_eq_right h, max_eq_right (Real.exp_le_exp.mpr (neg_le_neg h))]
    rw [h]
    exact hExp.sup (integrable_const _)
  have hYeBound : (∫ ω, Real.exp (-Y ω) ∂μ) ≤ M + Real.exp (-z) := by
    refine (integral_mono (g := fun ω => Real.exp (-X ω) + Real.exp (-z)) hYe (hExp.add (integrable_const (Real.exp (-z)))) (fun ω => ?_)).trans ?_
    · dsimp [Y]
      rcases le_total (X ω) z with h | h
      · rw [min_eq_left h]
        exact le_add_of_nonneg_right (Real.exp_nonneg _)
      · rw [min_eq_right h]
        exact le_add_of_nonneg_left (Real.exp_nonneg _)
    · rw [integral_add hExp (integrable_const (Real.exp (-z)))]
      simpa using add_le_add_right hExpBound (Real.exp (-z))
  have hlower := integral_ge_of_lower_bound_off_event_exp_neg μ Y {ω | X ω ≤ z}
    z L p (M + Real.exp (-z)) (hm measurableSet_Iic) hY hYe
    (fun ω hω => by dsimp [Y]; exact le_min (lt_of_not_ge hω).le le_rfl)
    hL hprob hYeBound
  have hid : (∫ ω, |X ω - z| ∂μ) =
      (∫ ω, X ω ∂μ) + z - 2 * ∫ ω, Y ω ∂μ := by
    have hp : (fun ω => |X ω - z|) = fun ω => X ω + z - 2 * Y ω := by
      funext ω
      dsimp [Y]
      rcases le_total (X ω) z with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
    rw [hp, integral_sub (f := fun ω => X ω + z) (g := fun ω => 2 * Y ω)
      (hX.add (integrable_const z)) (hY.const_mul 2),
      integral_add hX (integrable_const z), integral_const_mul]
    simp
  rw [hid]
  linarith

/-- Exponentially small lower tails and an asymptotic upper mean force `L¹`
convergence on arbitrary diverging positive scales. The laws may vary.
The proof reuses the one-sided exponential estimate rather than assuming
uniform integrability or a higher moment. -/
theorem tendsto_eLpNorm_one_div_sub_of_lower_tails_and_upper_mean
    {ι Ω : Type*} [MeasurableSpace Ω] {l : Filter ι}
    (μ : ι → Measure Ω) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (X : ι → Ω → ℝ) {L : ι → ℝ} {c A : ℝ}
    (hL : Tendsto L l atTop) (hm : ∀ i, Measurable (X i))
    (hX : ∀ᶠ i in l, Integrable (X i) (μ i))
    (hExp : ∀ᶠ i in l, Integrable (fun ω => Real.exp (-X i ω)) (μ i))
    (hExpBound : ∀ᶠ i in l, (∫ ω, Real.exp (-X i ω) ∂μ i) ≤ Real.exp (A * L i))
    (hTail : ∀ z < c, ∃ p : ℝ, 0 < p ∧ ∀ᶠ i in l,
      (μ i).real {ω | X i ω ≤ z * L i} ≤ Real.exp (-p * L i))
    (hmean : ∀ ε > 0, ∀ᶠ i in l, (∫ ω, X i ω / L i ∂μ i) ≤ c + ε) :
    Tendsto (fun i => eLpNorm (fun ω => X i ω / L i - c) 1 (μ i)) l (𝓝 0) := by
  have hnorm : Tendsto (fun i => ∫ ω, |X i ω / L i - c| ∂μ i) l (𝓝 0) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Eventually.of_forall fun i => ha.trans_le (integral_nonneg fun _ => abs_nonneg _)
    · intro ε hε
      let δ := ε / 8
      let z := c - δ
      have hδ : 0 < δ := div_pos hε (by norm_num)
      obtain ⟨p, hp, hprob⟩ := hTail z (by dsimp [z]; linarith)
      let q := max (max A (-z)) 0 + 1
      have hq : 0 < q := by dsimp [q]; linarith [le_max_right (max A (-z)) 0]
      have hAq : A - q < 0 := by
        have h := (le_max_left A (-z)).trans (le_max_left (max A (-z)) 0)
        dsimp [q]; linarith
      have hzq : -z - q < 0 := by
        have h := (le_max_right A (-z)).trans (le_max_left (max A (-z)) 0)
        dsimp [q]; linarith
      have hpow (r : ℝ) (hr : r < 0) : Tendsto (fun i => Real.exp (r * L i)) l (𝓝 0) :=
        Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg hr).2 hL)
      let R := fun i => 2 * (max z 0 + q) * Real.exp (-p * L i) +
        2 * (Real.exp ((A - q) * L i) + Real.exp ((-z - q) * L i)) / L i
      have hR : Tendsto R l (𝓝 0) := by
        have h := ((hpow (-p) (by linarith)).const_mul (2 * (max z 0 + q))).add
          ((((hpow (A - q) hAq).add (hpow (-z - q) hzq)).const_mul 2).mul hL.inv_tendsto_atTop)
        simpa [R, div_eq_mul_inv] using h
      filter_upwards [hX, hExp, hExpBound, hprob, hmean δ hδ,
        hL.eventually_gt_atTop 0, hR.eventually (Iio_mem_nhds (half_pos hε))]
        with i hi he heB hpB hmeanB hLi hRi
      let := hμ i
      have hfinite := integral_abs_sub_le_of_exp_neg_and_lower_tail (μ i) (X i) hi (hm i)
        he (mul_nonneg hq.le hLi.le) hpB heB
      have hcalc : (∫ ω, |X i ω - z * L i| ∂μ i) / L i ≤
          (∫ ω, X i ω / L i ∂μ i) - z + R i := by
        have h := div_le_div_of_nonneg_right hfinite hLi.le
        refine h.trans_eq ?_
        rw [integral_div]
        dsimp [R]
        have hmz : max (z * L i) 0 = max z 0 * L i := by
          rw [max_mul_of_nonneg z 0 hLi.le, zero_mul]
        rw [hmz]
        have heq (r : ℝ) : Real.exp (-(q * L i)) * Real.exp (r * L i) =
            Real.exp ((r - q) * L i) := by
          rw [← Real.exp_add]; congr 1; ring
        have hprod : Real.exp (-(q * L i)) *
            (Real.exp (A * L i) + Real.exp (-(z * L i))) =
            Real.exp ((A - q) * L i) + Real.exp ((-z - q) * L i) := by
          rw [mul_add, heq A, show -(z * L i) = (-z) * L i by ring, heq (-z)]
        rw [show 2 * Real.exp (-(q * L i)) *
          (Real.exp (A * L i) + Real.exp (-(z * L i))) =
          2 * (Real.exp (-(q * L i)) *
          (Real.exp (A * L i) + Real.exp (-(z * L i)))) by ring, hprod]
        field_simp
        ring
      have hpoint : (∫ ω, |X i ω / L i - c| ∂μ i) ≤
          (∫ ω, |X i ω - z * L i| ∂μ i) / L i + δ := by
        have habs : Integrable (fun ω => |X i ω - z * L i|) (μ i) :=
          (hi.sub (integrable_const _)).abs
        have hInt := integral_mono (f := fun ω => |X i ω / L i - c|)
          (g := fun ω => |X i ω - z * L i| / L i + δ) ((hi.div_const (L i)).sub (integrable_const c)).abs
          ((habs.div_const (L i)).add (integrable_const δ)) (fun ω => ?_)
        · simpa only [integral_add (habs.div_const (L i)) (integrable_const δ),
            integral_div, integral_const, probReal_univ, one_smul] using hInt
        · have ht := abs_add_le (X i ω / L i - z) (z - c)
          rw [show X i ω / L i - z + (z - c) = X i ω / L i - c by ring] at ht
          have hz : |z - c| = δ := by dsimp [z]; rw [sub_sub_cancel_left, abs_neg, abs_of_pos hδ]
          rw [hz, show X i ω / L i - z = (X i ω - z * L i) / L i by field_simp,
            abs_div, abs_of_pos hLi] at ht
          exact ht
      change (∫ ω, |X i ω - z * L i| ∂μ i) / L i ≤ _ at hcalc
      have heps : 3 * δ + ε / 2 < ε := by dsimp [δ]; linarith
      dsimp [z] at hcalc hpoint
      linarith
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hnorm
  simp only [ENNReal.ofReal_zero] at h
  apply h.congr'
  filter_upwards [hX] with i hi
  change ENNReal.ofReal (∫ ω, |X i ω / L i - c| ∂μ i) = _
  have hi' : Integrable (fun ω => X i ω / L i - c) (μ i) :=
    (hi.div_const _).sub (integrable_const _)
  symm
  calc
    _ = ∫⁻ ω, ‖X i ω / L i - c‖ₑ ∂μ i :=
      eLpNorm_one_eq_lintegral_eNorm hi'.aestronglyMeasurable
    _ = ENNReal.ofReal (∫ ω, ‖X i ω / L i - c‖ ∂μ i) :=
      (ofReal_integral_norm_eq_lintegral_eNorm hi').symm
    _ = _ := by simp only [Real.norm_eq_abs]

end ProbabilityTheory

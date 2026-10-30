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
import Probability.Distributions.CharacteristicFunction.CosineDefect
import MeasureTheory.Measure.Levy.JumpRegions
import all Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Lemmas.Representation.ScaledBounds
import Analysis.SpecialFunctions.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Scaled small-jump moment bounds in the Lévy–Khintchine proof

## Internal proof declarations

* `scaledMeasure_small_second_moment_bounded` states that for some `C > 0`,
  `t⁻¹ ∫_{|x|<1} x² dμ_t ≤ C` for all sufficiently small `t > 0`.
* `scaled_second_moment_bounded_along_seq` transfers this estimate to any positive sequence
  `tₙ → 0`. `integrableOn_sq_smallJumpSet` supplies the finite-measure integrability step.
-/

section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder

namespace ProbabilityTheory

namespace ConvolutionSemigroup

variable (S : ConvolutionSemigroup)

/-! ### Phase 4 — Small jump analysis (second moment + quadratic expansion)

The key estimates for the "small jump" part `{|x| < 1}` of the Lévy-Khintchine formula.

**4.1 — Second moment bound:** From `charFun(μ_t)(ξ) = exp(tψ(ξ))`:
```
Re(1 - exp(tψ(ξ))) = ∫ (1 - cos(xξ)) dμ_t
```
On `{|x| < 1}` with `ξ = 1`: `1 - cos(x) ≥ (2/π²) x²` (Jordan's inequality), so
```
(2/π²) ∫_{|x|<1} x² dμ_t ≤ ∫(1-cos(x))dμ_t = Re(1-exp(tψ(1)))
```
Dividing by `t`: `(2/(π²t)) ∫_{|x|<1} x² dμ_t ≤ Re(-ψ(1)) + o(1)`.

**4.2 — Quadratic expansion:** The integrand `exp(ixξ) - 1 - ixξ` satisfies
`|exp(iz)-1-iz| ≤ z²/2`, so the scaled integral on `{|x| < 1}` is controlled by
the second moment, giving convergence of a subsequence. -/

/-- The scaled quantity `t⁻¹ · Re(1 - exp(t·z))` converges to `Re(-z)` as `t → 0`.
This follows from `Complex.tendsto_exp_mul_real_div` composed with the continuous Re projection. -/
private lemma tendsto_inv_mul_re_one_sub_exp (z : ℂ) :
    Tendsto (fun t : ℝ => t⁻¹ * (1 - exp (↑t * z)).re) (𝓝[≠] 0) (𝓝 (-z).re) := by
  -- Step 1: (exp(tz)-1)/t → z, so (1-exp(tz))/t → -z
  have h2 : Tendsto (fun t : ℝ => (1 - exp ((↑t : ℂ) * z)) / (↑t : ℂ))
      (𝓝[≠] 0) (𝓝 (-z)) :=
    (Complex.tendsto_exp_mul_real_div z).neg.congr fun t => by
      show -((exp ((↑t : ℂ) * z) - 1) / (↑t : ℂ)) = _; ring
  -- Step 2: Take Re (continuous), get Re((1-exp(tz))/t) → Re(-z)
  have h3 := (Complex.continuous_re.tendsto _).comp h2
  -- Step 3: Re(w/↑t) = t⁻¹ · Re(w) for real t
  exact h3.congr fun t => by
    simp only [Function.comp_def]
    by_cases ht : t = 0
    · simp [ht]
    · rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm,
        Complex.re_ofReal_mul]

/-- For each `t > 0`, the scaled second moment is bounded by a multiple of
`t⁻¹ · Re(1 - exp(tψ(1)))`. Uses the charFun identity and the cos lower bound. -/
private lemma second_moment_le_scaled_re (t : {t : ℝ // 0 < t}) :
    2 / Real.pi ^ 2 * (t.val⁻¹ * ∫ x in smallJumpSet, x ^ 2 ∂(S.measure t : Measure ℝ)) ≤
      t.val⁻¹ * (1 - exp (↑t.val * S.exponent 1)).re := by
  -- charFun(μ_t)(1) = exp(t·ψ(1))
  have hcf : charFun (S.measure t : Measure ℝ) 1 = exp (↑t.val * S.exponent 1) := by
    exact S.charFun_eq t 1
  -- Re(1 - charFun(μ_t)(1)) = ∫ (1-cos x) dμ_t
  have hre : (1 - exp (↑t.val * S.exponent 1)).re =
      ∫ x, (1 - Real.cos (1 * x)) ∂(S.measure t : Measure ℝ) := by
    calc
      (1 - exp (↑t.val * S.exponent 1)).re =
          1 - (charFun (S.measure t : Measure ℝ) 1).re := by
        rw [← hcf]
        simp
      _ = cosineDefectIntegral (S.measure t : Measure ℝ) 1 :=
        (cosineDefectIntegral_eq_one_sub_charFun_re (S.measure t : Measure ℝ) 1).symm
      _ = ∫ x, (1 - Real.cos (1 * x)) ∂(S.measure t : Measure ℝ) := rfl
  rw [hre]; simp only [one_mul]
  -- Goal: 2/π² * (t⁻¹ * ∫_smallJumpSet x²) ≤ t⁻¹ * ∫ (1 - cos x)
  rw [show 2 / Real.pi ^ 2 * (t.val⁻¹ * ∫ x in smallJumpSet, x ^ 2 ∂(S.measure t : Measure ℝ)) =
    t.val⁻¹ * (2 / Real.pi ^ 2 * ∫ x in smallJumpSet, x ^ 2 ∂(S.measure t : Measure ℝ)) from by ring]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.mpr t.prop))
  -- Goal: 2/π² * ∫_smallJumpSet x² ≤ ∫ (1 - cos x)
  have hpi_bound : ∀ x : ℝ, x ∈ smallJumpSet → 2 / Real.pi ^ 2 * x ^ 2 ≤ 1 - Real.cos x := by
    intro x hx
    have hangle : |x| ≤ Real.pi :=
      le_of_lt (lt_of_lt_of_le (mem_smallJumpSet.mp hx)
        (le_trans (by norm_num : (1 : ℝ) ≤ 2) Real.two_le_pi))
    linarith [Real.cos_le_one_sub_mul_cos_sq hangle]
  have hint_sq : IntegrableOn (fun x => 2 / Real.pi ^ 2 * x ^ 2) smallJumpSet
      (S.measure t : Measure ℝ) :=
    Integrable.of_bound
      ((continuous_const.mul (continuous_pow 2)).aestronglyMeasurable)
      (2 / Real.pi ^ 2)
      (by filter_upwards [ae_restrict_mem measurableSet_smallJumpSet] with x hx
          have habs : |x| < 1 := mem_smallJumpSet.mp hx
          have hx_sq : x ^ 2 ≤ 1 := by
            nlinarith [sq_abs x, mul_le_of_le_one_right (abs_nonneg x) habs.le]
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (sq_nonneg x))]
          calc 2 / Real.pi ^ 2 * x ^ 2
              ≤ 2 / Real.pi ^ 2 * 1 := mul_le_mul_of_nonneg_left hx_sq (by positivity)
            _ = 2 / Real.pi ^ 2 := mul_one _)
  have hint_cos : IntegrableOn (fun x => 1 - Real.cos x) smallJumpSet
      (S.measure t : Measure ℝ) :=
    (Integrable.of_bound
      ((continuous_const.sub Real.continuous_cos).aestronglyMeasurable)
      2 (ae_of_all _ fun x => by
        simp only [Real.norm_eq_abs, Pi.sub_apply, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one x))]
        linarith [Real.neg_one_le_cos x])).integrableOn
  calc 2 / Real.pi ^ 2 * ∫ x in smallJumpSet, x ^ 2 ∂(S.measure t : Measure ℝ)
      = ∫ x in smallJumpSet, 2 / Real.pi ^ 2 * x ^ 2 ∂(S.measure t : Measure ℝ) :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ x in smallJumpSet, (1 - Real.cos x) ∂(S.measure t : Measure ℝ) :=
        setIntegral_mono_on hint_sq hint_cos measurableSet_smallJumpSet hpi_bound
    _ ≤ ∫ x, (1 - Real.cos x) ∂(S.measure t : Measure ℝ) :=
        setIntegral_le_integral
          (Integrable.of_bound
            ((continuous_const.sub Real.continuous_cos).aestronglyMeasurable)
            2 (ae_of_all _ fun x => by
              simp only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one x))]
              linarith [Real.neg_one_le_cos x]))
          (ae_of_all _ fun x => sub_nonneg.mpr (Real.cos_le_one _))

lemma scaledMeasure_small_second_moment_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ (t : {t : ℝ // 0 < t}) in comap Subtype.val (𝓝[>] (0 : ℝ)),
      t.val⁻¹ * ∫ x in smallJumpSet, x ^ 2 ∂(S.measure t : Measure ℝ) ≤ C := by
  set L := (-(S.exponent 1)).re
  -- t⁻¹ * Re(1 - exp(tψ(1))) → L as t → 0+
  have htend : Tendsto (fun (t : ℝ) => t⁻¹ * (1 - exp ((t : ℂ) * S.exponent 1)).re)
      (𝓝[>] (0 : ℝ)) (𝓝 L) :=
    (tendsto_inv_mul_re_one_sub_exp (S.exponent 1)).mono_left
      (nhdsWithin_mono (0 : ℝ) fun _ hx => ne_of_gt hx)
  -- Eventually ≤ |L| + 1
  have hevt : ∀ᶠ (r : ℝ) in 𝓝[>] (0 : ℝ),
      r⁻¹ * (1 - exp ((r : ℂ) * S.exponent 1)).re ≤ |L| + 1 :=
    (htend.eventually (Iio_mem_nhds (by linarith [le_abs_self L]))).mono
      fun _ h => le_of_lt h
  refine ⟨Real.pi ^ 2 / 2 * (|L| + 1), by positivity, ?_⟩
  exact (hevt.comap Subtype.val).mono fun t ht => by
    -- ht : t.val⁻¹ * Re(1 - exp(t.val·ψ(1))) ≤ |L| + 1
    have hle := le_trans (second_moment_le_scaled_re S t) ht
    -- hle : 2/π² * (t⁻¹ * ∫ x²) ≤ |L| + 1
    -- Multiply by π²/2 ≥ 0 and cancel
    have hfactor := mul_le_mul_of_nonneg_left hle
      (show (0 : ℝ) ≤ Real.pi ^ 2 / 2 from by positivity)
    rw [← mul_assoc, show Real.pi ^ 2 / 2 * (2 / Real.pi ^ 2) = 1 from by
      field_simp, one_mul] at hfactor
    exact hfactor

/-- The scaled second moment on `smallJumpSet` is eventually bounded along **any** positive-real
sequence tending to `0`. Direct consequence of `scaledMeasure_small_second_moment_bounded`,
pulled back along the subtype-valued sequence. -/
lemma scaled_second_moment_bounded_along_seq
    {t_seq : ℕ → {t : ℝ // 0 < t}} (ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      (t_seq n).val⁻¹ * ∫ x in smallJumpSet, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ) ≤ C := by
  obtain ⟨C, hC_pos, hC⟩ := S.scaledMeasure_small_second_moment_bounded
  refine ⟨C, hC_pos, ?_⟩
  -- Pull back the eventually statement along the sequence t_seq.
  have htseq_filter : Tendsto t_seq atTop (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) := by
    rw [Filter.tendsto_comap_iff]
    refine tendsto_nhdsWithin_iff.mpr ⟨ht, ?_⟩
    exact Filter.Eventually.of_forall (fun n => (t_seq n).prop)
  exact htseq_filter.eventually hC

/-! ### Phase 5: Drift extraction (first moment limit + drift contribution)

**5.1 — Drift limit:** The scaled first moment on `{|x| < 1}` converges along `t_n → 0`,
defining the drift `b`. This follows by subtracting the large-jump, quadratic, and remainder
contributions from the total limit `ψ(ξ)`.

**5.2 — Drift contribution:** The linear term `∫ (x · ξ · I) dμ_t` factors as
`ξ · I · ∫ x dμ_t`, so after scaling by `1/t` and taking the limit, contributes `b · ξ · I`
to the decomposition. -/

/-- `x²` is integrable on `smallJumpSet` against any finite measure (bounded by `1` there). -/
lemma integrableOn_sq_smallJumpSet (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IntegrableOn (fun x => x ^ 2) smallJumpSet μ := by
  refine IntegrableOn.of_bound (measure_lt_top _ _) ?_ 1 ?_
  · exact ((continuous_pow 2).measurable.aemeasurable.aestronglyMeasurable).restrict
  · exact (ae_restrict_mem measurableSet_smallJumpSet).mono (fun x hx => by
      have hxlt : |x| < 1 := mem_smallJumpSet.mp hx
      simp only [Real.norm_eq_abs]
      have h2 : x ^ 2 < 1 := by
        have h3 : |x| ^ 2 < 1 := pow_lt_one₀ (abs_nonneg x) hxlt two_ne_zero
        rwa [sq_abs] at h3
      rw [abs_of_nonneg (sq_nonneg x)]; linarith)

end ConvolutionSemigroup

end ProbabilityTheory

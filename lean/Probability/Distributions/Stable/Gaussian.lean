import Probability.Distributions.Stable.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
# Gaussian laws as stable laws

The centered Gaussian law is strictly stable with exponent two.  This file
connects mathlib's Gaussian distribution API to the abstract stable-law
predicate.  Small-deviation normalizations are handled in the Mogulskii
specialization layer.
-/

open Filter MeasureTheory
open scoped NNReal

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

end ProbabilityTheory

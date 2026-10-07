/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Analysis.Fourier.CosineTauberian.FrequencyAverage
public import Probability.Distributions.CharacteristicFunction.CosineDefect
public import Probability.Distributions.CharacteristicFunction.Symmetrization
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Frequency averaging for probability cosine defects

The averaged squared cosine kernel detects the tail of the measure whose
cosine defect is being averaged. For an increment law's squared-modulus
characteristic defect, that measure is its symmetrization (the law of the
difference of two independent copies), not the original increment law.
-/

open MeasureTheory Set
open scoped Interval
open Analysis.Fourier.CosineTauberian

@[expose] public section

namespace ProbabilityTheory

/-- Exact frequency-averaging identity. The factor `2` follows from
`4 (1 - cos z) - (1 - cos (2 z)) = 2 (1 - cos z)^2`. -/
theorem intervalIntegral_four_cosineDefect_sub_double
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ} :
    (∫ t in (1 : ℝ)..2,
      (4 * cosineDefectIntegral μ (t / x) -
        cosineDefectIntegral μ ((2 * t) / x))) =
      2 * ∫ y, cosineSquareFrequencyAverage (y / x) ∂μ := by
  let f : ℝ → ℝ → ℝ := fun t y => (1 - Real.cos (t * (y / x))) ^ 2
  let _ : IsFiniteMeasure (volume.restrict (uIoc (1 : ℝ) 2)) := by
    rw [uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    infer_instance
  have hfmeas : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict (uIoc (1 : ℝ) 2)).prod μ) := by
    exact (by fun_prop : Measurable (Function.uncurry f)).aestronglyMeasurable
  have hbound : ∀ᵐ p ∂((volume.restrict (uIoc (1 : ℝ) 2)).prod μ),
      ‖Function.uncurry f p‖ ≤ 4 := by
    filter_upwards [] with p
    change |(1 - Real.cos (p.1 * (p.2 / x))) ^ 2| ≤ 4
    rw [abs_of_nonneg (sq_nonneg _)]
    have hcoslo := Real.neg_one_le_cos (p.1 * (p.2 / x))
    have hcoshi := Real.cos_le_one (p.1 * (p.2 / x))
    nlinarith
  have hf : Integrable (Function.uncurry f)
      ((volume.restrict (uIoc (1 : ℝ) 2)).prod μ) :=
    Integrable.of_bound hfmeas 4 hbound
  have hswap :
      (∫ t in (1 : ℝ)..2, ∫ y, f t y ∂μ) =
        ∫ y, (∫ t in (1 : ℝ)..2, f t y) ∂μ := by
    convert intervalIntegral_integral_swap
      (a := (1 : ℝ)) (b := 2) (f := f) hf using 1
  have hcosInt (u : ℝ) : Integrable
      (fun y : ℝ => Real.cos (u * y)) μ := by
    exact (integrable_const (1 : ℝ)).mono' (by fun_prop)
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs]
        exact Real.abs_cos_le_one _)
  have hdefInt (u : ℝ) : Integrable
      (fun y : ℝ => 1 - Real.cos (u * y)) μ := by
    exact (integrable_const (1 : ℝ)).sub (hcosInt u)
  have hpoint (t : ℝ) :
      4 * cosineDefectIntegral μ (t / x) -
          cosineDefectIntegral μ ((2 * t) / x) =
        2 * ∫ y, f t y ∂μ := by
    have hscalar (y : ℝ) :
        4 * (1 - Real.cos ((t / x) * y)) -
            (1 - Real.cos (((2 * t) / x) * y)) =
          2 * (1 - Real.cos (t * (y / x))) ^ 2 := by
      have hz : (t / x) * y = t * (y / x) := by ring
      have hdouble : ((2 * t) / x) * y = 2 * (t * (y / x)) := by ring
      rw [hz, hdouble, Real.cos_two_mul]
      ring
    calc
      _ = 4 * (∫ y, 1 - Real.cos ((t / x) * y) ∂μ) -
          ∫ y, 1 - Real.cos (((2 * t) / x) * y) ∂μ := by
            rw [cosineDefectIntegral, cosineDefectIntegral]
      _ = ∫ y, (4 * (1 - Real.cos ((t / x) * y)) -
            (1 - Real.cos (((2 * t) / x) * y)) : ℝ) ∂μ := by
            rw [← integral_const_mul, ← integral_sub
              ((hdefInt _).const_mul 4) (hdefInt _)]
      _ = ∫ y, 2 * f t y ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with y
            simpa [f] using hscalar y
      _ = 2 * ∫ y, f t y ∂μ := by rw [integral_const_mul]
  have houter :
      (∫ t in (1 : ℝ)..2,
        (4 * cosineDefectIntegral μ (t / x) -
          cosineDefectIntegral μ ((2 * t) / x))) =
        2 * ∫ t in (1 : ℝ)..2, ∫ y, f t y ∂μ := by
    calc
      _ = ∫ t in (1 : ℝ)..2, 2 * ∫ y, f t y ∂μ := by
            apply intervalIntegral.integral_congr
            intro t _
            exact hpoint t
      _ = 2 * ∫ t in (1 : ℝ)..2, ∫ y, f t y ∂μ := by
            rw [intervalIntegral.integral_const_mul]
  calc
    _ = 2 * ∫ t in (1 : ℝ)..2, ∫ y, f t y ∂μ := houter
    _ = 2 * ∫ y, (∫ t in (1 : ℝ)..2, f t y) ∂μ := by
          exact congrArg (fun z : ℝ => 2 * z) hswap
    _ = 2 * ∫ y, cosineSquareFrequencyAverage (y / x) ∂μ := by
          congr 1

private theorem cosineSquareFrequencyAverage_nonneg (z : ℝ) :
    0 ≤ cosineSquareFrequencyAverage z := by
  exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
    (fun t => sq_nonneg (1 - Real.cos (t * z)))

private theorem cosineSquareFrequencyAverage_le_four (z : ℝ) :
    cosineSquareFrequencyAverage z ≤ 4 := by
  let f : ℝ → ℝ := fun t => (1 - Real.cos (t * z)) ^ 2
  have hfcont : Continuous f := by fun_prop
  have hf : IntervalIntegrable f volume 1 2 := hfcont.intervalIntegrable 1 2
  have hconst : IntervalIntegrable (fun _ : ℝ => (4 : ℝ)) volume 1 2 :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on
    (by norm_num : (1 : ℝ) ≤ 2) hf hconst (by
      intro t ht
      have hcoslo := Real.neg_one_le_cos (t * z)
      have hcoshi := Real.cos_le_one (t * z)
      nlinarith)
  have hconstInt : (∫ t in (1 : ℝ)..2, (4 : ℝ)) = 4 := by
    rw [intervalIntegral.integral_const]
    norm_num [smul_eq_mul]
  simpa [cosineSquareFrequencyAverage, f, hconstInt] using hmono

/-- A uniform coercive bound for the closed two-sided tail by the
frequency-averaged cosine defect. The law in this statement is the same law
whose cosine defect appears in the integral. -/
theorem exists_pos_closedAbsTail_le_cosineDefectFrequencyAverage
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ} (hx : 0 < x) :
    ∃ c : ℝ, 0 < c ∧
      2 * c * μ.real {y : ℝ | x ≤ |y|} ≤
        ∫ t in (1 : ℝ)..2,
          (4 * cosineDefectIntegral μ (t / x) -
            cosineDefectIntegral μ ((2 * t) / x)) := by
  obtain ⟨c, hc, hcoercive⟩ :=
    exists_pos_cosineSquareFrequencyAverage_lower_bound
  let A : Set ℝ := {y : ℝ | x ≤ |y|}
  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_le measurable_const continuous_abs.measurable
  have hkernel_meas : AEStronglyMeasurable
      (fun y : ℝ => cosineSquareFrequencyAverage (y / x)) μ := by
    have hdiv : Continuous (fun y : ℝ => y / x) := continuous_id.div_const x
    exact (continuous_cosineSquareFrequencyAverage.comp hdiv).aestronglyMeasurable
  have hkernel_bound : ∀ᵐ y ∂μ,
      ‖cosineSquareFrequencyAverage (y / x)‖ ≤ 4 := by
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (cosineSquareFrequencyAverage_nonneg _)]
    exact cosineSquareFrequencyAverage_le_four _
  have hkernel_int : Integrable
      (fun y : ℝ => cosineSquareFrequencyAverage (y / x)) μ :=
    Integrable.of_bound hkernel_meas 4 hkernel_bound
  have hindicator : Integrable (A.indicator (fun _ : ℝ => c)) μ :=
    (integrable_const c).indicator hA
  have hindicator_eq :
      (∫ y, A.indicator (fun _ : ℝ => c) y ∂μ) = c * μ.real A := by
    rw [integral_indicator_const _ hA]
    simp [smul_eq_mul, mul_comm]
  have hpointwise (y : ℝ) :
      A.indicator (fun _ : ℝ => c) y ≤ cosineSquareFrequencyAverage (y / x) := by
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy]
      have hratio : 1 ≤ |y / x| := by
        rw [abs_div, abs_of_pos hx]
        calc
          1 = x / x := (div_self hx.ne').symm
          _ ≤ |y| / x := div_le_div_of_nonneg_right (by simpa [A] using hy) hx.le
      exact hcoercive (y / x) hratio
    · rw [Set.indicator_of_notMem hy]
      exact cosineSquareFrequencyAverage_nonneg _
  have htail : c * μ.real A ≤
      ∫ y, cosineSquareFrequencyAverage (y / x) ∂μ := by
    calc
      _ = ∫ y, A.indicator (fun _ : ℝ => c) y ∂μ := hindicator_eq.symm
      _ ≤ ∫ y, cosineSquareFrequencyAverage (y / x) ∂μ :=
        integral_mono_ae hindicator hkernel_int (ae_of_all μ hpointwise)
  refine ⟨c, hc, ?_⟩
  rw [intervalIntegral_four_cosineDefect_sub_double μ]
  calc
    2 * c * μ.real {y : ℝ | x ≤ |y|} = 2 * (c * μ.real A) := by
      simp [A, mul_assoc]
    _ ≤ 2 * ∫ y, cosineSquareFrequencyAverage (y / x) ∂μ :=
      mul_le_mul_of_nonneg_left htail (by norm_num)

/-- For a characteristic-function norm defect, the tail detected by
frequency averaging is the tail of the symmetrized law (the difference of
two iid variables). -/
theorem exists_pos_symmetrizedClosedAbsTail_le_normDefectFrequencyAverage
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {x : ℝ} (hx : 0 < x) :
    ∃ c : ℝ, 0 < c ∧
      2 * c * (symmetrizedMeasure ν).real {y : ℝ | x ≤ |y|} ≤
        ∫ t in (1 : ℝ)..2,
          (4 * (1 - ‖charFun ν (t / x)‖ ^ 2) -
            (1 - ‖charFun ν ((2 * t) / x)‖ ^ 2)) := by
  obtain ⟨c, hc, htail⟩ :=
    exists_pos_closedAbsTail_le_cosineDefectFrequencyAverage
      (symmetrizedMeasure ν) hx
  refine ⟨c, hc, ?_⟩
  apply le_of_le_of_eq htail
  apply intervalIntegral.integral_congr
  intro t _
  simp only [cosineDefectIntegral_symmetrizedMeasure]

end ProbabilityTheory

end

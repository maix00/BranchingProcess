/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Representation
public import Probability.Process.Levy.Measure.Scaling
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Integrand

/-!
# Scaling of the compensated Lévy–Khintchine integrand

Changing spatial scale changes the truncation radius. The resulting
correction is linear in the Fourier variable and therefore contributes only
to the drift. This file records the pointwise identity and its integrability.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- The difference between compensating before and after a dilation. -/
noncomputable def compensationDifference (a ξ x : ℝ) : ℂ :=
  levyCompensatedIntegrand (a * ξ) x -
    levyCompensatedIntegrand ξ (a * x)

/-- The compensation difference contains no exponential term. -/
theorem compensationDifference_eq (a ξ x : ℝ) :
    compensationDifference a ξ x =
      ((a * x * ξ : ℝ) : ℂ) * Complex.I *
        ((if |a * x| < 1 then (1 : ℂ) else 0) -
          (if |x| < 1 then (1 : ℂ) else 0)) := by
  have harg : (x : ℂ) * (↑(a * ξ) : ℂ) * Complex.I =
      (↑(a * x) : ℂ) * (ξ : ℂ) * Complex.I := by
    push_cast
    ring
  by_cases hx : |x| < 1 <;> by_cases hax : |a * x| < 1 <;>
    simp only [compensationDifference, levyCompensatedIntegrand, harg, hx, hax,
      ite_true, ite_false, mul_one, mul_zero, sub_zero] <;> push_cast <;> ring

/-- The compensation correction is linear in the Fourier variable. -/
theorem compensationDifference_mul_freq (a ξ x : ℝ) :
    compensationDifference a ξ x =
      (ξ : ℂ) * compensationDifference a 1 x := by
  rw [compensationDifference_eq, compensationDifference_eq]
  push_cast
  ring

/-- The truncation correction has no real part. -/
theorem compensationDifference_re (a x : ℝ) :
    (compensationDifference a 1 x).re = 0 := by
  rw [compensationDifference_eq]
  split_ifs <;> simp

/-- The truncation correction is integrable for a nonzero dilation. -/
theorem _root_.MeasureTheory.IsLevyMeasure.integrable_compensationDifference
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν)
    {a : ℝ} (ha : a ≠ 0) (ξ : ℝ) :
    Integrable (compensationDifference a ξ) ν := by
  have hf : Measurable (fun x : ℝ => a * x) := by fun_prop
  have hνa : MeasureTheory.IsLevyMeasure (ν.map fun x => a * x) := hν.map_mul ha
  have hfirst := integrable_levyCompensatedIntegrand hν (a * ξ)
  have hsecond : Integrable (fun x => levyCompensatedIntegrand ξ (a * x)) ν := by
    exact (integrable_levyCompensatedIntegrand hνa ξ).comp_measurable hf
  exact hfirst.sub hsecond

/-- The integrated correction remains linear in frequency; its value at one
determines the drift adjustment at every frequency. -/
theorem _root_.MeasureTheory.IsLevyMeasure.integral_compensationDifference_mul_freq
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν)
    {a : ℝ} (ha : a ≠ 0) (ξ : ℝ) :
    (∫ x, compensationDifference a ξ x ∂ν) =
      (ξ : ℂ) * ∫ x, compensationDifference a 1 x ∂ν := by
  have hint := hν.integrable_compensationDifference ha 1
  simp_rw [compensationDifference_mul_freq a ξ]
  exact integral_const_mul _ _

/-- The integrated truncation correction changes only the drift. -/
theorem _root_.MeasureTheory.IsLevyMeasure.integral_compensationDifference_re
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν)
    {a : ℝ} (ha : a ≠ 0) :
    (∫ x, compensationDifference a 1 x ∂ν).re = 0 := by
  change RCLike.re (∫ x, compensationDifference a 1 x ∂ν) = 0
  rw [← integral_re (hν.integrable_compensationDifference ha 1)]
  change (∫ x, (compensationDifference a 1 x).re ∂ν) = 0
  simp_rw [compensationDifference_re]
  simp

/-- Spatial scaling of the jump term, including the exact correction caused
by the fixed truncation radius in the canonical Lévy–Khintchine formula. -/
theorem _root_.MeasureTheory.IsLevyMeasure.integral_compensated_scale
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν)
    {a : ℝ} (ha : a ≠ 0) (ξ : ℝ) :
    (∫ x, levyCompensatedIntegrand (a * ξ) x ∂ν) =
      (∫ y, levyCompensatedIntegrand ξ y ∂(ν.map fun x => a * x)) +
        (ξ : ℂ) * ∫ x, compensationDifference a 1 x ∂ν := by
  have hf : Measurable (fun x : ℝ => a * x) := by fun_prop
  have hνa : MeasureTheory.IsLevyMeasure (ν.map fun x => a * x) := hν.map_mul ha
  have hfirst := integrable_levyCompensatedIntegrand hν (a * ξ)
  have hsecond : Integrable (fun x => levyCompensatedIntegrand ξ (a * x)) ν :=
    (integrable_levyCompensatedIntegrand hνa ξ).comp_measurable hf
  have hdiff := hν.integrable_compensationDifference ha ξ
  calc
    (∫ x, levyCompensatedIntegrand (a * ξ) x ∂ν) =
        (∫ x, levyCompensatedIntegrand ξ (a * x) ∂ν) +
          (∫ x, compensationDifference a ξ x ∂ν) := by
      rw [show (∫ x, compensationDifference a ξ x ∂ν) =
          (∫ x, levyCompensatedIntegrand (a * ξ) x ∂ν) -
            (∫ x, levyCompensatedIntegrand ξ (a * x) ∂ν) from
        integral_sub hfirst hsecond]
      abel
    _ = (∫ y, levyCompensatedIntegrand ξ y ∂(ν.map fun x => a * x)) +
          (ξ : ℂ) * ∫ x, compensationDifference a 1 x ∂ν := by
      rw [integral_map hf.aemeasurable
        (measurable_levyCompensatedIntegrand ξ).aestronglyMeasurable,
        hν.integral_compensationDifference_mul_freq ha ξ]

/-- Canonical Lévy–Khintchine triple after a nonzero spatial dilation. The
drift correction accounts for changing the fixed radius-one truncation. -/
noncomputable def LevyKhintchineTriple.scale
    (T : LevyKhintchineTriple) (a : ℝ) (ha : a ≠ 0) :
    LevyKhintchineTriple where
  drift := a * T.drift +
    (∫ x, compensationDifference a 1 x ∂T.levyMeasure).im
  gaussianVariance := Real.toNNReal (a ^ 2) * T.gaussianVariance
  levyMeasure := T.levyMeasure.map fun x => a * x
  isLevyMeasure := MeasureTheory.IsLevyMeasure.map_mul T.isLevyMeasure ha

/-- Scaling the triple agrees exactly with scaling its characteristic
exponent, including the truncation-dependent drift. -/
theorem LevyKhintchineTriple.scale_exponent
    (T : LevyKhintchineTriple) (a : ℝ) (ha : a ≠ 0) (ξ : ℝ) :
    (T.scale a ha).exponent ξ = T.exponent (a * ξ) := by
  let C : ℂ := ∫ x, compensationDifference a 1 x ∂T.levyMeasure
  have hCre : C.re = 0 :=
    T.isLevyMeasure.integral_compensationDifference_re ha
  have hC : C = (C.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hCre]
  have hjump := T.isLevyMeasure.integral_compensated_scale ha ξ
  unfold LevyKhintchineTriple.exponent LevyKhintchineTriple.scale
  dsimp only
  rw [hjump]
  change _ = _ + (_ + ((ξ : ℂ) * C))
  rw [hC]
  rw [show (∫ x, compensationDifference a 1 x ∂T.levyMeasure) = C from rfl]
  simp only [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg a)]
  push_cast
  ring

/-- Scaling the intensity of a Lévy–Khintchine triple by a nonnegative real
number scales all three components by that number. -/
noncomputable def LevyKhintchineTriple.scaleIntensity
    (T : LevyKhintchineTriple) (c : ℝ) (_hc : 0 ≤ c) :
    LevyKhintchineTriple where
  drift := c * T.drift
  gaussianVariance := Real.toNNReal c * T.gaussianVariance
  levyMeasure := ENNReal.ofReal c • T.levyMeasure
  isLevyMeasure :=
    T.isLevyMeasure.smul ENNReal.ofReal_ne_top

/-- The intensity-scaled triple has exponent `c ψ`. -/
theorem LevyKhintchineTriple.scaleIntensity_exponent
    (T : LevyKhintchineTriple) (c : ℝ) (hc : 0 ≤ c) (ξ : ℝ) :
    (T.scaleIntensity c hc).exponent ξ = (c : ℂ) * T.exponent ξ := by
  unfold LevyKhintchineTriple.exponent LevyKhintchineTriple.scaleIntensity
  dsimp only
  rw [integral_smul_measure]
  simp only [ENNReal.toReal_ofReal hc, Complex.real_smul,
    NNReal.coe_mul, Real.coe_toNNReal c hc]
  push_cast
  ring

end ProbabilityTheory

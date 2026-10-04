/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Probability.Process.Levy.Exponent.Scaling

/-!
# The uncompensated drift in a finite-variation Lévy exponent

The truncation used by the canonical Lévy–Khintchine triple is the open unit
ball.  When the small-jump displacement is integrable, its integral can be
removed from the canonical drift.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Set

/-- The displacement kept by the canonical radius-one compensation. -/
noncomputable def smallJumpDisplacement (x : ℝ) : ℝ :=
  if |x| < 1 then x else 0

/-- The small-jump displacement is integrable under the usual finite-variation
condition. -/
theorem integrable_smallJumpDisplacement {ν : Measure ℝ}
    (h : IntegrableOn (fun x : ℝ => x) {x : ℝ | |x| ≤ 1} ν) :
    Integrable smallJumpDisplacement ν := by
  have hsub : Ioo (-1 : ℝ) 1 ⊆ {x : ℝ | |x| ≤ 1} := by
    intro x hx
    simp only [mem_Ioo, mem_ofPred_eq] at hx ⊢
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hint := h.mono_set hsub
  have hs : MeasurableSet (Ioo (-1 : ℝ) 1) := measurableSet_Ioo
  have heq : smallJumpDisplacement = (Ioo (-1 : ℝ) 1).indicator id := by
    funext x
    by_cases hx : |x| < 1
    · have hmem : x ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp hx
      simp [smallJumpDisplacement, hx, Set.indicator_of_mem hmem]
    · have hmem : x ∉ Ioo (-1 : ℝ) 1 := by simpa [abs_lt] using hx
      simp [smallJumpDisplacement, hx, Set.indicator_of_notMem hmem]
  rw [heq]
  exact hint.integrable_indicator hs

/-- The correction caused by scaling the canonical truncation is the
difference of two small-jump displacements. -/
theorem compensationDifference_eq_smallJumpDisplacement (a x : ℝ) :
    compensationDifference a 1 x =
      ((smallJumpDisplacement (a * x) - a * smallJumpDisplacement x : ℝ) : ℂ) *
        Complex.I := by
  rw [compensationDifference_eq]
  by_cases hx : |x| < 1 <;> by_cases hax : |a * x| < 1 <;>
    simp only [smallJumpDisplacement, hx, hax, ite_true, ite_false,
      mul_one, mul_zero, sub_zero, zero_sub] <;> push_cast <;> ring

/-- The imaginary part of the truncation correction is the change in the
first small-jump moment under spatial dilation. -/
theorem _root_.MeasureTheory.IsLevyMeasure.integral_compensationDifference_im
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν)
    {a : ℝ} (ha : a ≠ 0)
    (hsmall : Integrable smallJumpDisplacement ν)
    (hscaled : Integrable smallJumpDisplacement (ν.map fun x => a * x)) :
    (∫ x, compensationDifference a 1 x ∂ν).im =
      (∫ y, smallJumpDisplacement y ∂(ν.map fun x => a * x)) -
        a * ∫ x, smallJumpDisplacement x ∂ν := by
  have hf : Measurable (fun x : ℝ => a * x) := by fun_prop
  have hcomp : Integrable (fun x => smallJumpDisplacement (a * x)) ν :=
    hscaled.comp_measurable hf
  have hmul : Integrable (fun x => a * smallJumpDisplacement x) ν :=
    hsmall.const_mul a
  rw [integral_map hf.aemeasurable hscaled.aestronglyMeasurable]
  change RCLike.im (∫ x, compensationDifference a 1 x ∂ν) = _
  rw [← integral_im (hν.integrable_compensationDifference ha 1)]
  simp_rw [compensationDifference_eq_smallJumpDisplacement]
  have him (x : ℝ) :
      RCLike.im (((smallJumpDisplacement (a * x) - a * smallJumpDisplacement x : ℝ) : ℂ) *
        Complex.I) = smallJumpDisplacement (a * x) - a * smallJumpDisplacement x := by
    change (((smallJumpDisplacement (a * x) - a * smallJumpDisplacement x : ℝ) : ℂ) *
      Complex.I).im = _
    simp
  simp_rw [him]
  rw [integral_sub hcomp hmul, integral_const_mul]

/-- The jump integrand without a radius-one compensation term. -/
noncomputable def levyUncompensatedIntegrand (ξ x : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) * (ξ : ℂ) * Complex.I) - 1

theorem levyUncompensatedIntegrand_eq (ξ x : ℝ) :
    levyUncompensatedIntegrand ξ x =
      levyCompensatedIntegrand ξ x +
        (smallJumpDisplacement x : ℂ) * (ξ : ℂ) * Complex.I := by
  by_cases hx : |x| < 1 <;>
    simp [levyUncompensatedIntegrand, levyCompensatedIntegrand,
      smallJumpDisplacement, hx]

/-- The uncompensated integrand is integrable under a finite-variation
small-jump condition. -/
theorem _root_.MeasureTheory.IsLevyMeasure.integrable_uncompensatedIntegrand
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν)
    (hsmall : Integrable smallJumpDisplacement ν) (ξ : ℝ) :
    Integrable (levyUncompensatedIntegrand ξ) ν := by
  have hlinear : Integrable
      (fun x => (smallJumpDisplacement x : ℂ) * (ξ : ℂ) * Complex.I) ν :=
    ((hsmall.ofReal).mul_const (ξ : ℂ)).mul_const Complex.I
  have heq : levyUncompensatedIntegrand ξ =
      fun x => levyCompensatedIntegrand ξ x +
        (smallJumpDisplacement x : ℂ) * (ξ : ℂ) * Complex.I := by
    funext x
    exact levyUncompensatedIntegrand_eq ξ x
  rw [heq]
  exact (integrable_levyCompensatedIntegrand hν ξ).add hlinear

/-- Removing the compensation term from the jump integral adds back the
small-jump first moment. -/
theorem _root_.MeasureTheory.IsLevyMeasure.integral_uncompensatedIntegrand
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν)
    (hsmall : Integrable smallJumpDisplacement ν) (ξ : ℝ) :
    (∫ x, levyUncompensatedIntegrand ξ x ∂ν) =
      (∫ x, levyCompensatedIntegrand ξ x ∂ν) +
        ((∫ x, smallJumpDisplacement x ∂ν : ℝ) : ℂ) * (ξ : ℂ) * Complex.I := by
  simp_rw [levyUncompensatedIntegrand_eq]
  have hlinear : Integrable
      (fun x => (smallJumpDisplacement x : ℂ) * (ξ : ℂ) * Complex.I) ν :=
    ((hsmall.ofReal).mul_const (ξ : ℂ)).mul_const Complex.I
  rw [integral_add (integrable_levyCompensatedIntegrand hν ξ) hlinear]
  simp only [integral_mul_const]
  rw [integral_complex_ofReal]

end ProbabilityTheory

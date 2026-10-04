/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.LevyMeasure.Variation
public import Probability.Process.Levy.Exponent.FiniteVariation

/-!
# Vanishing uncompensated drift below index one

For a strictly stable law with `α < 1`, the small-jump first moment exists.
The canonical Lévy–Khintchine drift equals this moment, so the drift in the
uncompensated finite-variation representation vanishes.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- The small-jump first moment under the canonical open-unit-ball
truncation. -/
noncomputable def LevyKhintchineTriple.smallJumpMean (T : LevyKhintchineTriple) : ℝ :=
  ∫ x, smallJumpDisplacement x ∂T.levyMeasure

/-- The drift after removing the canonical small-jump compensation. -/
noncomputable def LevyKhintchineTriple.uncompensatedDrift (T : LevyKhintchineTriple) : ℝ :=
  T.drift - T.smallJumpMean

/-- A strictly stable law of index below one has zero drift in the
uncompensated finite-variation convention. -/
theorem IsStrictlyAlphaStable.uncompensatedDrift_eq_zero
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1) :
    T.uncompensatedDrift = 0 := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hsmall : Integrable smallJumpDisplacement T.levyMeasure :=
    integrable_smallJumpDisplacement (h.levyMeasure_integrableOn_small T hT hα)
  have hmap := h.levyMeasure_map_mul T hT htwo
  have hscaled : Integrable smallJumpDisplacement
      (T.levyMeasure.map fun x => (2 : ℝ) * x) := by
    rw [hmap]
    exact hsmall.smul_measure ENNReal.ofReal_ne_top
  have him := T.isLevyMeasure.integral_compensationDifference_im
    (by norm_num : (2 : ℝ) ≠ 0) hsmall hscaled
  have hmean : (∫ x, smallJumpDisplacement x
      ∂(T.levyMeasure.map fun x => (2 : ℝ) * x)) =
      (2 ^ α) * T.smallJumpMean := by
    rw [hmap, integral_smul_measure]
    simp only [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos htwo α).le,
      smul_eq_mul, LevyKhintchineTriple.smallJumpMean]
  have htriple := h.scale_triple_eq T hT htwo
  have hdrift := congrArg LevyKhintchineTriple.drift htriple
  change (2 : ℝ) * T.drift +
      (∫ x, compensationDifference 2 1 x ∂T.levyMeasure).im =
        (2 ^ α) * T.drift at hdrift
  rw [him, hmean] at hdrift
  change (2 : ℝ) * T.drift +
      ((2 ^ α) * T.smallJumpMean - 2 * T.smallJumpMean) =
        (2 ^ α) * T.drift at hdrift
  have hcoeff : (2 : ℝ) ^ α < 2 := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt
      (by norm_num : (1 : ℝ) < 2) hα
  unfold LevyKhintchineTriple.uncompensatedDrift
  have hmul : ((2 : ℝ) - 2 ^ α) * (T.drift - T.smallJumpMean) = 0 := by
    nlinarith [hdrift]
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr (ne_of_gt hcoeff))

/-- Below index one, the stable characteristic exponent is exactly the
uncompensated jump integral of its own Lévy measure. -/
theorem IsStrictlyAlphaStable.exponent_eq_integral_uncompensated
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1) (ξ : ℝ) :
    T.exponent ξ =
      ∫ x, levyUncompensatedIntegrand ξ x ∂T.levyMeasure := by
  have hsmall : Integrable smallJumpDisplacement T.levyMeasure :=
    integrable_smallJumpDisplacement (h.levyMeasure_integrableOn_small T hT hα)
  have hgauss : T.gaussianVariance = 0 :=
    h.gaussianVariance_eq_zero_of_lt_two T hT (by linarith)
  have hdrift : T.drift = T.smallJumpMean := by
    have hzero := h.uncompensatedDrift_eq_zero T hT hα
    exact sub_eq_zero.mp hzero
  rw [T.isLevyMeasure.integral_uncompensatedIntegrand hsmall ξ]
  rw [LevyKhintchineTriple.exponent_def, hgauss, hdrift]
  simp only [NNReal.coe_zero, Complex.ofReal_zero, zero_mul, zero_div,
    sub_zero]
  unfold LevyKhintchineTriple.smallJumpMean
  ring

/-- The characteristic function of the given stable law has the exact
finite-variation pure-jump form. -/
theorem IsStrictlyAlphaStable.charFun_eq_exp_integral_uncompensated
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1) (ξ : ℝ) :
    charFun μ ξ = Complex.exp
      (∫ x, levyUncompensatedIntegrand ξ x ∂T.levyMeasure) := by
  rw [hT ξ, h.exponent_eq_integral_uncompensated T hT hα ξ]

end ProbabilityTheory

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Basic
public import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Defs
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Scaling

import Probability.Distributions.Stable.Exponent.Basic
import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Uniqueness

/-!
# Scaling the Lévy measure of a strictly stable law

Uniqueness of the Lévy–Khintchine triple transfers exponent homogeneity to
the Gaussian coefficient and the Lévy measure. The drift field already
contains the precise truncation correction from the generic scaling theory.

Writing `ν = T.levyMeasure`, strict `α`-stability gives the measure identity

\[
\nu\circ(x\mapsto ax)^{-1}
=\operatorname{ENNReal.ofReal}(a^\alpha)\,\nu
\qquad(a>0).
\]

The Gaussian coefficient `G = T.gaussianVariance` obeys both spatial scaling
laws,

\[
\operatorname{toNNReal}(a^2)G
=\operatorname{toNNReal}(a^\alpha)G.
\]

When `α<2`, these distinct powers force `G=0`.

## Public declarations

* `IsStrictlyAlphaStable.scale_triple_eq` identifies `T.scale a` with
  `T.scaleIntensity (a^α)`.
* `IsStrictlyAlphaStable.levyMeasure_map_mul` states
  `Measure.map (a * ·) T.levyMeasure = a^α • T.levyMeasure`.
* `IsStrictlyAlphaStable.gaussianVariance_scale` equates the quadratic and
  `α`-power scalings of the Gaussian coefficient; for `α < 2`,
  `IsStrictlyAlphaStable.gaussianVariance_eq_zero_of_lt_two` gives coefficient
  zero.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- The spatially scaled and intensity-scaled triples agree. -/
theorem IsStrictlyAlphaStable.scale_triple_eq
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    {a : ℝ} (ha : 0 < a) :
    T.scale a ha.ne' = T.scaleIntensity (a ^ α) (Real.rpow_pos_of_pos ha α).le := by
  apply LevyKhintchineTriple.ext_of_exponent_eq
  intro ξ
  rw [T.scale_exponent a ha.ne' ξ,
    T.scaleIntensity_exponent (a ^ α) (Real.rpow_pos_of_pos ha α).le ξ]
  exact h.exponent_scale T hT ha ξ

/-- The Lévy measure of a strictly stable law is homogeneous as a measure,
including multiplicities and atoms. -/
theorem IsStrictlyAlphaStable.levyMeasure_map_mul
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    {a : ℝ} (ha : 0 < a) :
    T.levyMeasure.map (fun x => a * x) =
      ENNReal.ofReal (a ^ α) • T.levyMeasure := by
  have heq := h.scale_triple_eq T hT ha
  exact congrArg LevyKhintchineTriple.levyMeasure heq

/-- The Gaussian coefficient obeys both the quadratic scaling law and the
stable `α`-scaling law. -/
theorem IsStrictlyAlphaStable.gaussianVariance_scale
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    {a : ℝ} (ha : 0 < a) :
    Real.toNNReal (a ^ 2) * T.gaussianVariance =
      Real.toNNReal (a ^ α) * T.gaussianVariance := by
  have heq := h.scale_triple_eq T hT ha
  exact congrArg LevyKhintchineTriple.gaussianVariance heq

/-- For a strictly stable law of index below two, the Gaussian component of
its Lévy–Khintchine triple vanishes. -/
theorem IsStrictlyAlphaStable.gaussianVariance_eq_zero_of_lt_two
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 2) : T.gaussianVariance = 0 := by
  have heq := h.gaussianVariance_scale T hT (show (0 : ℝ) < 2 by norm_num)
  have hlt : Real.toNNReal ((2 : ℝ) ^ α) < Real.toNNReal ((2 : ℝ) ^ (2 : ℝ)) := by
    rw [Real.toNNReal_lt_toNNReal_iff (by norm_num)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hα
  rcases (mul_eq_mul_right_iff).mp heq with hcoeff | hzero
  · exact False.elim (ne_of_gt hlt (by simpa using hcoeff))
  · exact hzero

end ProbabilityTheory

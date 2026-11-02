/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Stable probability laws

This file defines real-valued stable laws through the distribution of weighted
sums of two independent copies.  It does not choose a density or a
characteristic-function parametrization, and keeps the stability predicates at
the probability-measure level without introducing a random-variable wrapper.

For `0 < α ≤ 2`, the scale and maps are

\[
\kappa_\alpha(a,b)=(a^\alpha+b^\alpha)^{1/\alpha},\qquad
S_{a,b}(x,y)=ax+by,\qquad A_{r,c}(x)=rx+c.
\]

An `α`-stable probability measure `μ` satisfies, for each `a,b>0`,

\[
(\mu\otimes\mu)\circ S_{a,b}^{-1}
=\mu\circ A_{\kappa_\alpha(a,b),c}^{-1}
\quad\text{for some }c\in\mathbb R.
\]

Strict stability uses the same scaling with `c=0`.

## Public declarations

* `alphaStableScale α a b = (a^α + b^α)^(1/α)`,
  `weightedSum a b (x,y) = a*x + b*y`, and
  `affine scale shift x = scale*x + shift` define the scaling and maps used
  in the stability predicates.
* `IsAlphaStable α μ` requires `0 < α ≤ 2`, a nondegenerate probability law,
  and `(μ.prod μ).map (weightedSum a b) = μ.map (affine (alphaStableScale α a b) shift)`
  for every `a,b > 0` and some shift.
* `IsStrictlyAlphaStable α μ` uses the same parameter range and nondegeneracy
  conditions, with the scaling identity
  `(μ.prod μ).map (weightedSum a b) = μ.map (alphaStableScale α a b ·)`.
* `alphaStableScale_two_sq` and `alphaStableScale_two_nonneg` give
  `alphaStableScale 2 a b ^ 2 = a ^ 2 + b ^ 2` and
  `0 ≤ alphaStableScale 2 a b`.
* `measurable_weightedSum` and `measurable_affine` establish measurability of
  the two maps. `IsAlphaStable.alpha_pos`, `.alpha_le_two`, `.isProbabilityMeasure`,
  and `.nondegenerate` project the corresponding hypotheses; strict stability
  implies ordinary stability and has matching probability and nondegeneracy
  projections.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

/-- The scale forced by the stability exponent for two positive weights. -/
noncomputable def alphaStableScale (α a b : ℝ) : ℝ :=
  (a ^ α + b ^ α) ^ (1 / α)

/-- The strictly stable scale at index two satisfies the Pythagorean identity. -/
theorem alphaStableScale_two_sq (a b : ℝ) :
    alphaStableScale 2 a b ^ 2 = a ^ 2 + b ^ 2 := by
  rw [alphaStableScale, Real.rpow_two, Real.rpow_two]
  rw [show (1 / (2 : ℝ)) = ((2 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.rpow_inv_natCast_pow (n := 2) (by positivity) (by norm_num)

/-- The strictly stable scale at index two is nonnegative. -/
theorem alphaStableScale_two_nonneg (a b : ℝ) :
    0 ≤ alphaStableScale 2 a b := by
  rw [alphaStableScale, Real.rpow_two, Real.rpow_two]
  exact Real.rpow_nonneg (by positivity) _

/-- The weighted sum of two real coordinates. -/
def weightedSum (a b : ℝ) (p : ℝ × ℝ) : ℝ :=
  a * p.1 + b * p.2

/-- An affine rescaling of a real coordinate. -/
def affine (scale shift x : ℝ) : ℝ :=
  scale * x + shift

theorem measurable_weightedSum (a b : ℝ) : Measurable (weightedSum a b) := by
  exact (measurable_const.mul measurable_fst).add
    (measurable_const.mul measurable_snd)

theorem measurable_affine (scale shift : ℝ) :
    Measurable (affine scale shift) := by
  exact (measurable_const.mul measurable_id).add measurable_const

/-- A probability law is `α`-stable if every positive weighted sum of two
independent copies is an affine image of the same law with the scale dictated
by `α`.  The shift is allowed to depend on the two weights. -/
def IsAlphaStable (α : ℝ) (μ : Measure ℝ) : Prop :=
  0 < α ∧ α ≤ 2 ∧ IsProbabilityMeasure μ ∧
    (¬ ∃ x : ℝ, μ = Measure.dirac x) ∧
    ∀ a b : ℝ, 0 < a → 0 < b →
      ∃ shift : ℝ,
        (μ.prod μ).map (weightedSum a b) =
          μ.map (affine (alphaStableScale α a b) shift)

/-- Strict stability is the same scaling identity without a translation. -/
def IsStrictlyAlphaStable (α : ℝ) (μ : Measure ℝ) : Prop :=
  0 < α ∧ α ≤ 2 ∧ IsProbabilityMeasure μ ∧
    (¬ ∃ x : ℝ, μ = Measure.dirac x) ∧
    ∀ a b : ℝ, 0 < a → 0 < b →
      (μ.prod μ).map (weightedSum a b) =
        μ.map (fun x => alphaStableScale α a b * x)

namespace IsAlphaStable

theorem alpha_pos {α : ℝ} {μ : Measure ℝ} (h : IsAlphaStable α μ) :
    0 < α := h.1

theorem alpha_le_two {α : ℝ} {μ : Measure ℝ} (h : IsAlphaStable α μ) :
    α ≤ 2 := h.2.1

theorem isProbabilityMeasure {α : ℝ} {μ : Measure ℝ}
    (h : IsAlphaStable α μ) : IsProbabilityMeasure μ := h.2.2.1

theorem nondegenerate {α : ℝ} {μ : Measure ℝ}
    (h : IsAlphaStable α μ) : ¬ ∃ x : ℝ, μ = Measure.dirac x :=
  h.2.2.2.1

end IsAlphaStable

namespace IsStrictlyAlphaStable

theorem isAlphaStable {α : ℝ} {μ : Measure ℝ}
    (h : IsStrictlyAlphaStable α μ) : IsAlphaStable α μ := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  intro a b ha hb
  refine ⟨0, ?_⟩
  unfold affine
  simp only [add_zero]
  exact h.2.2.2.2 a b ha hb

theorem isProbabilityMeasure {α : ℝ} {μ : Measure ℝ}
    (h : IsStrictlyAlphaStable α μ) : IsProbabilityMeasure μ := h.2.2.1

theorem nondegenerate {α : ℝ} {μ : Measure ℝ}
    (h : IsStrictlyAlphaStable α μ) : ¬ ∃ x : ℝ, μ = Measure.dirac x :=
  h.2.2.2.1

end IsStrictlyAlphaStable

end ProbabilityTheory

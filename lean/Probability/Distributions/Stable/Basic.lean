module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Stable probability laws

This file defines stable laws through the distribution of weighted sums of
two independent copies.  It does not choose a density or a characteristic
function parametrization, so it covers discrete proof interfaces and future
multivariate generalizations without introducing a random-variable wrapper.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

/-- The scale forced by the stability exponent for two positive weights. -/
noncomputable def alphaStableScale (α a b : ℝ) : ℝ :=
  (a ^ α + b ^ α) ^ (1 / α)

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

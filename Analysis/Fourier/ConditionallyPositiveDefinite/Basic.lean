/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Authors: LeanLevy Contributors
-/
module

public import Analysis.Fourier.PositiveDefinite

/-!
# Conditionally positive definite functions on additive groups

## Public declarations

* `IsConditionallyPositiveDefinite`: for `ψ : G → ℂ`, every finite quadratic form
  `Q = ∑ i, ∑ j, conj (c i) * c j * ψ (x i - x j)` is real and nonnegative
  whenever `∑ i, c i = 0`.
* `IsConditionallyPositiveDefinite.add`, `.const`, and `.smul_nonneg`: closure under
  addition, constant functions, and multiplication by nonnegative real scalars.
* `IsConditionallyPositiveDefinite.re_nonneg`: the real part of this quadratic form
  is nonnegative.
* `IsConditionallyPositiveDefinite.imaginary_additive`: for an additive map `φ : G →+ ℝ`,
  the function `x ↦ a φ(x) I` is conditionally positive definite (its zero-sum quadratic form vanishes).
* `IsConditionallyPositiveDefinite.neg_sq`: the function `x ↦ -x²` on `ℝ` is conditionally
  positive definite.
* `IsPositiveDefinite.cpd_sub_one`: if `g` is positive definite, then `g - 1` is
  conditionally positive definite.

This exponent sign convention is used in Schoenberg's theorem. See A. S. Holevo,
“Conditionally Positive Definite Functions in Quantum Probability,” *Proceedings of the
International Congress of Mathematicians* (Berkeley, 1986), vol. 2, pp. 1011–1020,
Introduction, opening paragraph. That paragraph states the group Schoenberg
correspondence and its Hermitian condition; the proceedings scan is available at
<https://sites.math.rutgers.edu/~zeilberg/akherim/icm1986.pdf>.
-/

@[expose] public section

open Complex ComplexConjugate Finset
open scoped ComplexOrder

/-- A function `ψ : G → ℂ` is conditionally positive definite when every finite
quadratic form `∑ᵢ ∑ⱼ conj(cᵢ) cⱼ ψ(xᵢ - xⱼ)` is real and nonnegative for weights
satisfying `∑ᵢ cᵢ = 0`.

This is the exponent sign convention used by Schoenberg's correspondence:
`exp(t * ψ)` is positive definite for `t ≥ 0` when `ψ` is Hermitian. -/
def IsConditionallyPositiveDefinite {G : Type*} [AddGroup G] (ψ : G → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
    ∑ i, c i = 0 →
    0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ψ (x i - x j)

namespace IsConditionallyPositiveDefinite

variable {G : Type*} [AddGroup G] {ψ₁ ψ₂ ψ : G → ℂ}

/-- The sum of two conditionally positive definite functions is conditionally positive
definite. -/
theorem add (h₁ : IsConditionallyPositiveDefinite ψ₁)
    (h₂ : IsConditionallyPositiveDefinite ψ₂) :
    IsConditionallyPositiveDefinite (fun x => ψ₁ x + ψ₂ x) := by
  intro n x c hc
  have e : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        (ψ₁ (x i - x j) + ψ₂ (x i - x j)))
      = (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ψ₁ (x i - x j))
        + (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ψ₂ (x i - x j)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  exact add_nonneg (h₁ n x c hc) (h₂ n x c hc)

/-- Every constant function is conditionally positive definite: its quadratic form
factors through the vanishing sum of the weights. -/
theorem const (z : ℂ) : IsConditionallyPositiveDefinite (fun _ : G => z) := by
  intro n x c hc
  have hsum : ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j = 0 := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    simp [hc]
  have hform : ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * z = 0 := by
    calc
      _ = (∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j) * z := by
        rw [Finset.sum_mul]
        congr 1
        ext i
        rw [Finset.sum_mul]
      _ = 0 := by rw [hsum, zero_mul]
  rw [hform]

/-- Multiplication by a nonnegative real scalar preserves conditional positive
definiteness. -/
theorem smul_nonneg {a : ℝ} (h : IsConditionallyPositiveDefinite ψ) (ha : 0 ≤ a) :
    IsConditionallyPositiveDefinite (fun x => (a : ℂ) * ψ x) := by
  intro n x c hc
  have e : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        ((a : ℂ) * ψ (x i - x j)))
      = (a : ℂ) * ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ψ (x i - x j) := by
    rw [show (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        ((a : ℂ) * ψ (x i - x j)))
        = (a : ℂ) * ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ψ (x i - x j) from ?_]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  have haC : 0 ≤ (a : ℂ) := by
    rw [Complex.nonneg_iff]
    simp [ha]
  exact mul_nonneg haC (h n x c hc)

/-- The real part of a conditionally positive definite quadratic form is nonnegative. -/
theorem re_nonneg (h : IsConditionallyPositiveDefinite ψ) (n : ℕ)
    (x : Fin n → G) (c : Fin n → ℂ) (hc : ∑ i, c i = 0) :
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ψ (x i - x j)).re := by
  exact (Complex.nonneg_iff.mp (h n x c hc)).1

end IsConditionallyPositiveDefinite

private lemma double_sum_conj_mul_eq_zero {n : ℕ} {c : Fin n → ℂ}
    (hc : ∑ i, c i = 0) :
    ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j = 0 := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp [hc]

namespace IsPositiveDefinite

variable {G : Type*} [AddGroup G]

/-- If `g` is positive definite, then `g - 1` is conditionally positive definite:
the constant term vanishes on weights whose sum is zero. -/
theorem cpd_sub_one {g : G → ℂ} (hg : IsPositiveDefinite g) :
    IsConditionallyPositiveDefinite (fun x => g x - 1) := by
  intro n x c hc
  have e : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (g (x i - x j) - 1))
      = (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * g (x i - x j))
        - (∑ i, ∑ j, starRingEnd ℂ (c i) * c j) := by
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [e, double_sum_conj_mul_eq_zero hc, sub_zero]
  exact hg n x c

end IsPositiveDefinite

namespace IsConditionallyPositiveDefinite

/-- If `φ : G →+ ℝ` is additive, then `x ↦ a·φ(x)·I` is conditionally positive
definite: its quadratic form factors through the zero-sum condition on the coefficients. -/
theorem imaginary_additive {G : Type*} [AddGroup G] (φ : G →+ ℝ) (a : ℝ) :
    IsConditionallyPositiveDefinite (fun x : G => (a : ℂ) * ↑(φ x) * I) := by
  intro n ξ c hc
  have hconj0 : (∑ i, starRingEnd ℂ (c i)) = 0 := by rw [← _root_.map_sum, hc, map_zero]
  have expand : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        ((↑(φ (ξ i)) : ℂ) - ↑(φ (ξ j))))
      = (∑ i, starRingEnd ℂ (c i) * (↑(φ (ξ i)) : ℂ)) * (∑ j, c j)
        - (∑ i, starRingEnd ℂ (c i)) * (∑ j, c j * (↑(φ (ξ j)) : ℂ)) := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsum0 : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      ((a : ℂ) * ↑(φ (ξ i - ξ j)) * I)) = 0 := by
    have factored : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
          ((a : ℂ) * ↑(φ (ξ i - ξ j)) * I))
        = (a : ℂ) * I * (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
          ((↑(φ (ξ i)) : ℂ) - ↑(φ (ξ j)))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_sub]
      push_cast; ring
    rw [factored, expand, hc, hconj0]; ring
  rw [hsum0]

/-- The function `ξ ↦ -ξ²` on `ℝ` is conditionally positive definite. On zero-sum
coefficients, its quadratic form is `2‖∑ⱼ cⱼ ξⱼ‖²`. -/
theorem neg_sq :
    IsConditionallyPositiveDefinite (fun ξ : ℝ => -((ξ : ℂ) ^ 2)) := by
  intro n ξ c hc
  set W : ℂ := ∑ j, c j * (↑(ξ j) : ℂ) with hW
  have hconj0 : (∑ i, starRingEnd ℂ (c i)) = 0 := by rw [← _root_.map_sum, hc, map_zero]
  have hcW : (∑ i, starRingEnd ℂ (c i) * (↑(ξ i) : ℂ)) = starRingEnd ℂ W := by
    rw [hW, _root_.map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, Complex.conj_ofReal]
  have A : (∑ i, ∑ j, -(starRingEnd ℂ (c i) * (↑(ξ i) : ℂ) ^ 2) * c j) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.mul_sum, hc, mul_zero]
  have B : (∑ i, ∑ j, 2 * (starRingEnd ℂ (c i) * (↑(ξ i) : ℂ)) *
      (c j * (↑(ξ j) : ℂ))) = 2 * starRingEnd ℂ W * W := by
    have hi : ∀ i, (∑ j, 2 * (starRingEnd ℂ (c i) * (↑(ξ i) : ℂ)) *
        (c j * (↑(ξ j) : ℂ))) = 2 * (starRingEnd ℂ (c i) * (↑(ξ i) : ℂ)) * W := by
      intro i; rw [hW, Finset.mul_sum]
    simp_rw [hi]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hcW]
  have C : (∑ i, ∑ j, -(starRingEnd ℂ (c i) * (c j * (↑(ξ j) : ℂ) ^ 2))) = 0 := by
    have hi : ∀ i, (∑ j, -(starRingEnd ℂ (c i) * (c j * (↑(ξ j) : ℂ) ^ 2)))
        = starRingEnd ℂ (c i) * (∑ j, -(c j * (↑(ξ j) : ℂ) ^ 2)) := by
      intro i; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    simp_rw [hi, ← Finset.sum_mul, hconj0, zero_mul]
  have key : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (-((↑(ξ i - ξ j) : ℂ) ^ 2)))
      = 2 * starRingEnd ℂ W * W := by
    have step : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (-((↑(ξ i - ξ j) : ℂ) ^ 2)))
        = (∑ i, ∑ j, (-(starRingEnd ℂ (c i) * (↑(ξ i) : ℂ) ^ 2) * c j
            + 2 * (starRingEnd ℂ (c i) * (↑(ξ i) : ℂ)) * (c j * (↑(ξ j) : ℂ))
            + -(starRingEnd ℂ (c i) * (c j * (↑(ξ j) : ℂ) ^ 2)))) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      push_cast; ring
    rw [step]
    rw [show (∑ i, ∑ j, (-(starRingEnd ℂ (c i) * (↑(ξ i) : ℂ) ^ 2) * c j
          + 2 * (starRingEnd ℂ (c i) * (↑(ξ i) : ℂ)) * (c j * (↑(ξ j) : ℂ))
          + -(starRingEnd ℂ (c i) * (c j * (↑(ξ j) : ℂ) ^ 2))))
        = (∑ i, ∑ j, -(starRingEnd ℂ (c i) * (↑(ξ i) : ℂ) ^ 2) * c j)
          + (∑ i, ∑ j, 2 * (starRingEnd ℂ (c i) * (↑(ξ i) : ℂ)) *
              (c j * (↑(ξ j) : ℂ)))
          + (∑ i, ∑ j, -(starRingEnd ℂ (c i) * (c j * (↑(ξ j) : ℂ) ^ 2)))
        from by simp_rw [Finset.sum_add_distrib]]
    rw [A, B, C]; ring
  rw [key]
  have hcomplex : (2 : ℂ) * starRingEnd ℂ W * W = (2 * Complex.normSq W : ℂ) := by
    rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self]
  rw [hcomplex]
  have hnorm : (0 : ℂ) ≤ (Complex.normSq W : ℂ) := by
    rw [Complex.nonneg_iff]
    exact ⟨Complex.normSq_nonneg W, by simp⟩
  have htwo : (0 : ℂ) ≤ 2 := by norm_num
  have hpos : (0 : ℂ) ≤ (2 * Complex.normSq W : ℂ) := mul_nonneg htwo hnorm
  rw [Complex.nonneg_iff]
  exact (Complex.nonneg_iff.mp hpos)

end IsConditionallyPositiveDefinite

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

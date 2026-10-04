/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Topology.Basic
import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-!
# Positive Definite Functions on Additive Groups

A function `φ : G → ℂ` on an additive group is **positive definite** if for every finite
sequence of points
`x₁, …, xₙ` and complex weights `c₁, …, cₙ`, the Hermitian form
`∑ᵢ ∑ⱼ c̄ᵢ cⱼ φ(xᵢ − xⱼ)` is nonneg (real and `≥ 0`).

## Main definitions

* `IsPositiveDefinite` — the positive-definiteness predicate.

## Main results

* `IsPositiveDefinite.re_nonneg` — `.re ≥ 0` (convenience corollary of definition).
* `IsPositiveDefinite.apply_zero_nonneg` — `φ(0).re ≥ 0`.
* `IsPositiveDefinite.conj_neg` — `φ(-t) = conj(φ(t))` (Hermitianness).
* `IsPositiveDefinite.mul` — Schur product: pointwise product of PD functions is PD.
* `IsPositiveDefinite.closure_pointwise` — pointwise limit of PD functions is PD.

-/

open Complex ComplexConjugate Finset Filter Topology Matrix
open scoped NNReal ENNReal ComplexOrder

/-- A function `φ : G → ℂ` is **positive definite** if for every `n`, points `x : Fin n → G`,
and weights `c : Fin n → ℂ`, the Hermitian form `∑ᵢ ∑ⱼ c̄ᵢ cⱼ φ(xᵢ − xⱼ)` is
nonneg (i.e. real and `≥ 0`).
-/
def IsPositiveDefinite {G : Type*} [AddGroup G] (φ : G → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
    0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * φ (x i - x j)

namespace IsPositiveDefinite

section AddGroup

variable {G : Type*} [AddGroup G]
variable {φ ψ : G → ℂ}

/-- The Hermitian form has nonneg `.re`. Convenience corollary of the definition. -/
theorem re_nonneg (hφ : IsPositiveDefinite φ) (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ) :
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * φ (x i - x j)).re :=
  (Complex.nonneg_iff.mp (hφ n x c)).1

/-- The Hermitian form has zero `.im`. Convenience corollary of the definition. -/
theorem im_eq_zero (hφ : IsPositiveDefinite φ) (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ) :
    (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * φ (x i - x j)).im = 0 :=
  (Complex.nonneg_iff.mp (hφ n x c)).2.symm

/-- `φ(0).re ≥ 0`. Specialise to `n = 1`, `c = 1`, `x = 0`. -/
theorem apply_zero_nonneg (hφ : IsPositiveDefinite φ) : 0 ≤ (φ 0).re := by
  have h := hφ.re_nonneg 1 (fun _ => 0) (fun _ => 1)
  simp [sub_self] at h
  exact h

/-- `φ(0)` is real. -/
theorem apply_zero_im (hφ : IsPositiveDefinite φ) : (φ 0).im = 0 := by
  have h := hφ.im_eq_zero 1 (fun _ => 0) (fun _ => 1)
  simp [sub_self] at h
  exact h

/-- A PD function is Hermitian: `φ(-t) = conj(φ(t))`. -/
theorem conj_neg (hφ : IsPositiveDefinite φ) (t : G) :
    φ (-t) = starRingEnd ℂ (φ t) := by
  -- Extract the 2×2 form's imaginary part being zero for any weights.
  -- Use points [0, t], so φ(0-t) = φ(-t), φ(t-0) = φ(t), φ(0-0) = φ(0), φ(t-t) = φ(0).
  have him : ∀ c₀ c₁ : ℂ,
      (starRingEnd ℂ c₀ * c₀ * φ 0 + starRingEnd ℂ c₀ * c₁ * φ (-t) +
      (starRingEnd ℂ c₁ * c₀ * φ t + starRingEnd ℂ c₁ * c₁ * φ 0)).im = 0 := by
    intro c₀ c₁
    have h := hφ.im_eq_zero 2 ![0, t] ![c₀, c₁]
    simp only [Fin.sum_univ_two] at h
    -- The h has Matrix.cons / vecHead / vecTail forms; let's normalize
    simp only [show (![0, t] : Fin 2 → G) 0 = 0 from rfl,
      show (![0, t] : Fin 2 → G) 1 = t from rfl,
      show (![c₀, c₁] : Fin 2 → ℂ) 0 = c₀ from rfl,
      show (![c₀, c₁] : Fin 2 → ℂ) 1 = c₁ from rfl, sub_self,
      show t - 0 = t from by simp, show 0 - t = -t from by simp] at h
    linarith
  have hφ0_im := hφ.apply_zero_im
  -- c₀ = 1, c₁ = 1: Im(φ(0) + φ(-t) + φ(t) + φ(0)) = 0
  have h11 := him 1 1
  simp only [map_one, one_mul] at h11
  have him_neg : (φ (-t)).im = -(φ t).im := by
    simp only [add_im] at h11; linarith [hφ0_im]
  -- c₀ = 1, c₁ = I gives Re(φ(-t)) = Re(φ(t))
  have hre_eq : (φ (-t)).re = (φ t).re := by
    have h1I := him 1 I
    simp only [map_one, one_mul, mul_one, conj_I] at h1I
    -- Expand the imaginary part of `h1I` using `I ^ 2 = -1`.
    have key := h1I
    rw [show (-I * I : ℂ) = 1 from by rw [neg_mul, ← sq, I_sq, neg_neg]] at key
    simp only [add_im, mul_im, I_re, I_im, neg_im, neg_re, one_im, one_re] at key
    linarith [hφ0_im]
  apply Complex.ext
  · exact hre_eq
  · simp only [conj_im]; linarith

/-- The PD matrix is positive semidefinite. -/
theorem pdMatrix_posSemidef (hφ : IsPositiveDefinite φ) (m : ℕ) (x : Fin m → G) :
    (Matrix.of fun i j : Fin m => φ (x i - x j)).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun c => ?_⟩
  · ext i j
    simp only [conjTranspose_apply, Matrix.of_apply, star_def]
    rw [show x j - x i = -(x i - x j) from by simp only [neg_sub], hφ.conj_neg,
      starRingEnd_self_apply]
  · change 0 ≤ dotProduct (star c) (mulVec (Matrix.of fun i j => φ (x i - x j)) c)
    have key : dotProduct (star c) (mulVec (Matrix.of fun i j => φ (x i - x j)) c) =
        ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * φ (x i - x j) := by
      simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def]
      congr 1; ext i
      rw [Finset.mul_sum]
      congr 1; ext j; ring
    rw [key]
    exact hφ m x c

/-- **Schur product theorem.** The pointwise product of two positive definite functions
is positive definite. This follows from Mathlib's Hadamard product theorem for positive
semidefinite matrices. -/
theorem mul (hφ : IsPositiveDefinite φ) (hψ : IsPositiveDefinite ψ) :
    IsPositiveDefinite (fun x => φ x * ψ x) := by
  intro m x c
  classical
  let A : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j => φ (x i - x j)
  let B : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j => ψ (x i - x j)
  have hAB : (A.hadamard B).PosSemidef :=
    (hφ.pdMatrix_posSemidef m x).hadamard (hψ.pdMatrix_posSemidef m x)
  have hquad := hAB.dotProduct_mulVec_nonneg c
  have hquad_eq : dotProduct (star c) ((A.hadamard B).mulVec c) =
      ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        (φ (x i - x j) * ψ (x i - x j)) := by
    simp only [dotProduct, mulVec, Matrix.hadamard_apply, A, B, Matrix.of_apply,
      Pi.star_apply, RCLike.star_def]
    congr 1
    ext i
    rw [Finset.mul_sum]
    congr 1
    ext j
    ring
  rw [hquad_eq] at hquad
  exact hquad

/-- Pointwise limit of positive definite functions is positive definite. -/
theorem closure_pointwise {φs : ℕ → G → ℂ} (hφs : ∀ n, IsPositiveDefinite (φs n))
    {φ : G → ℂ} (hlim : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x))) :
    IsPositiveDefinite φ := by
  intro n x c
  have htend : Tendsto (fun k => ∑ i, ∑ j,
      starRingEnd ℂ (c i) * c j * φs k (x i - x j)) atTop
      (𝓝 (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * φ (x i - x j))) := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (hlim (x i - x j)).const_mul _
  exact ge_of_tendsto htend (Eventually.of_forall fun k => hφs k n x c)

end AddGroup

variable {φ : ℝ → ℂ}

/-- For a positive definite function with `φ(0) = 1`, `‖φ(ξ)‖ ≤ 1`.

Proof sketch: Take `n = 2`, `x = (0, ξ)`, and `c = (1, -φ(ξ)/‖φ(ξ)‖)`.
Positive definiteness yields `0 ≤ 2 - 2‖φ(ξ)‖`, hence `‖φ(ξ)‖ ≤ 1`. The proof uses
the Hermitian symmetry `φ(-ξ) = conj(φ(ξ))`, which follows from positive definiteness. -/
theorem norm_le_one (hφ : IsPositiveDefinite φ) (h0 : φ 0 = 1) (ξ : ℝ) :
    ‖φ ξ‖ ≤ 1 := by
  by_cases hξ : φ ξ = 0
  · simp [hξ]
  have hnorm_pos : (0 : ℝ) < ‖φ ξ‖ := norm_pos_iff.mpr hξ
  have hpd := hφ.re_nonneg 2 ![0, ξ] ![↑‖φ ξ‖, -(φ ξ)]
  simp only [Fin.sum_univ_two,
    show (![0, ξ] : Fin 2 → ℝ) 0 = 0 from rfl,
    show (![0, ξ] : Fin 2 → ℝ) 1 = ξ from rfl,
    show (![↑‖φ ξ‖, -(φ ξ)] : Fin 2 → ℂ) 0 = ↑‖φ ξ‖ from rfl,
    show (![↑‖φ ξ‖, -(φ ξ)] : Fin 2 → ℂ) 1 = -(φ ξ) from rfl] at hpd
  simp only [sub_self, sub_zero, zero_sub, h0, hφ.conj_neg ξ, map_neg,
    Complex.conj_ofReal, mul_neg, neg_mul, neg_neg, mul_one] at hpd
  -- hpd : 0 ≤ (↑‖φ ξ‖ * ↑‖φ ξ‖ + -(↑‖φ ξ‖ * φ ξ * conj(φ ξ))
  --     + (-(conj(φ ξ) * ↑‖φ ξ‖ * φ ξ) + conj(φ ξ) * φ ξ)).re
  -- Replace conj*z products with normSq = ‖z‖²
  have hns : φ ξ * starRingEnd ℂ (φ ξ) = ↑(Complex.normSq (φ ξ)) := by
    rw [← Complex.mul_conj]
  have hns' : starRingEnd ℂ (φ ξ) * φ ξ = ↑(Complex.normSq (φ ξ)) :=
    Complex.normSq_eq_conj_mul_self.symm
  have hns_eq : (Complex.normSq (φ ξ) : ℝ) = ‖φ ξ‖ ^ 2 := Complex.normSq_eq_norm_sq _
  -- Reassociate and replace in hpd
  have hrw1 : ↑‖φ ξ‖ * φ ξ * starRingEnd ℂ (φ ξ) =
      ↑‖φ ξ‖ * ↑(Complex.normSq (φ ξ)) := by rw [mul_assoc, hns]
  have hrw2 : starRingEnd ℂ (φ ξ) * ↑‖φ ξ‖ * φ ξ =
      ↑‖φ ξ‖ * ↑(Complex.normSq (φ ξ)) := by
    rw [show starRingEnd ℂ (φ ξ) * ↑‖φ ξ‖ * φ ξ =
        ↑‖φ ξ‖ * (starRingEnd ℂ (φ ξ) * φ ξ) from by ring, hns']
  rw [hrw1, hrw2, hns'] at hpd
  -- Now hpd only involves ↑‖φ ξ‖ and ↑(normSq (φ ξ)) — all real-valued
  -- All terms are real-valued ofReal casts, so .re extracts the real part cleanly
  -- After rewriting, `hpd` is a real inequality in `‖φ ξ‖` and `normSq (φ ξ)`.
  -- where a = ‖φ ξ‖, c = normSq(φ ξ). These are all ofReal products.
  -- Extract .re from each ofReal product
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero] at hpd
  rw [hns_eq] at hpd
  -- This is `2 * ‖φ ξ‖ ^ 2 * (1 - ‖φ ξ‖) ≥ 0`; strict positivity gives the bound.
  nlinarith [sq_nonneg ‖φ ξ‖, sq_nonneg (‖φ ξ‖ - 1)]


end IsPositiveDefinite

namespace IsPositiveDefinite

/-- The exponential `ξ ↦ exp(-x·ξ·I)` is positive definite. Its quadratic form is
`Complex.normSq (∑ j, c j * exp(x * ξ j * I))`. -/
theorem exp_neg_ofReal_mul (x : ℝ) :
    IsPositiveDefinite (fun ξ : ℝ => Complex.exp (-(↑x * ↑ξ * I))) := by
  intro n pts c
  have hsum_eq : ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      Complex.exp (-(↑x * ↑(pts i - pts j) * I)) =
      ↑(Complex.normSq (∑ i, c i * Complex.exp (↑x * ↑(pts i) * I))) := by
    rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, ← exp_conj, conj_ofReal, conj_I, mul_neg]
    rw [show -(↑x * ↑(pts i - pts j) * I) =
        -(↑x * ↑(pts i) * I) + ↑x * ↑(pts j) * I from by push_cast; ring,
      exp_add]
    ring
  rw [hsum_eq]
  exact_mod_cast Complex.normSq_nonneg _

/-- The exponential `ξ ↦ exp(x·ξ·I)` is positive definite. -/
theorem exp_ofReal_mul (x : ℝ) :
    IsPositiveDefinite (fun ξ : ℝ => Complex.exp ((x : ℂ) * (ξ : ℂ) * I)) := by
  have h := exp_neg_ofReal_mul (-x)
  convert h using 1
  ext ξ
  congr 1
  push_cast
  ring

end IsPositiveDefinite

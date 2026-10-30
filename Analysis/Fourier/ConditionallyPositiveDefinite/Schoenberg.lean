/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Authors: LeanLevy Contributors
-/
module

public import Analysis.Fourier.ConditionallyPositiveDefinite.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Matrix.Order

/-!
# Schoenberg's theorem for conditionally positive definite functions

## Public declarations

* `IsConditionallyPositiveDefinite.schoenberg_exp`: on any additive group `G`, if
  `ψ : G → ℂ` is conditionally positive definite and Hermitian, then
  `x ↦ exp (t * ψ x)` is positive definite for every `t ≥ 0`.

The theorem is algebraic and requires no topology or continuity. Its group formulation
is stated by A. S. Holevo, “Conditionally Positive Definite Functions in Quantum
Probability,” *Proceedings of the International Congress of Mathematicians* (Berkeley,
1986), vol. 2, pp. 1011–1020, Introduction, opening paragraph. The proceedings scan is
available at <https://sites.math.rutgers.edu/~zeilberg/akherim/icm1986.pdf>. The proof
uses the anchored kernel and Mathlib's Schur product theorem for positive semidefinite
matrices.
-/

@[expose] public section

open Complex ComplexConjugate Finset Filter Topology Matrix
open scoped NNReal ENNReal ComplexOrder

/-! ## Schoenberg's theorem -/

/-- The normalized case of Schoenberg's theorem, used after subtracting `ψ 0`.

Our conditionally positive definite convention requires the zero-sum quadratic form
itself to be real and nonnegative. This matches the exponent convention where
`charFun = exp(ψ)`, so `exp(t * ψ)` is positive definite.

## Proof strategy

For conditionally positive definite `ψ` with `ψ(0) = 0` and
`ψ(-x) = conj (ψ(x))`, the anchored kernel
`Kᵢⱼ = ψ(xᵢ - xⱼ) - ψ(xᵢ) - conj(ψ(xⱼ))` is positive semidefinite. Its
entrywise exponential `exp(t * Kᵢⱼ)` is positive semidefinite by the Schur product
theorem applied to the power series. Factoring
`exp(t * ψ(xᵢ - xⱼ))` into this kernel and the two one-variable exponential factors
gives positive definiteness. The matrix result used is Mathlib's
`Matrix.PosSemidef.hadamard` from `Mathlib.Analysis.Matrix.Order`. -/
-- Helper: The conditionally positive definite kernel M_{ij} = ψ(ξᵢ-ξⱼ) - ψ(ξᵢ) - conj(ψ(ξⱼ)) is PD.
-- Proved by instantiating conditionally positive definite at n+1 points [0, ξ₁, ..., ξₙ] with weight c₀ = -∑ cᵢ.
-- Requires Hermitian symmetry ψ(-ξ) = conj(ψ(ξ)) to relate ψ(-ξⱼ) → conj(ψ(ξⱼ)).
private lemma cpd_kernel_pd
    {G : Type*} [AddGroup G] {ψ : G → ℂ}
    (hψ_cpd : IsConditionallyPositiveDefinite ψ) (hψ_zero : ψ 0 = 0)
    (hψ_herm : ∀ ξ, ψ (-ξ) = starRingEnd ℂ (ψ ξ))
    (n : ℕ) (ξ : Fin n → G) (c : Fin n → ℂ) :
    0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      (ψ (ξ i - ξ j) - ψ (ξ i) - starRingEnd ℂ (ψ (ξ j))) := by
  -- Proof: instantiate conditionally positive definite at (n+1) points [0, ξ₁, ..., ξₙ] with c₀ = -∑ cᵢ.
  -- The (n+1)-point sum expands (using ψ(0)=0 and ψ(-ξ)=conj(ψ(ξ))) to our kernel sum.
  -- .re ≥ 0 from conditionally positive definite; .im = 0 from kernel Hermitianness.
  rw [Complex.nonneg_iff]
  constructor
  · -- .re ≥ 0: the (n+1)-point conditionally positive definite sum with c₀ = -∑cᵢ, ξ₀ = 0 equals our kernel sum
    -- after simplification with ψ(0) = 0 and ψ(-ξⱼ) = conj(ψ(ξⱼ)).
    -- The block expansion:
    --   (0,0): |c₀|²ψ(0) = 0
    --   (0,j≥1): conj(c₀)·cⱼ·ψ(-ξⱼ) = -∑ₖ∑ⱼ conj(cₖ)cⱼ·conj(ψ(ξⱼ))
    --   (i≥1,0): conj(cᵢ)·c₀·ψ(ξᵢ) = -∑ᵢ∑ₖ conj(cᵢ)cₖ·ψ(ξᵢ)
    --   (i≥1,j≥1): ∑∑ conj(cᵢ)cⱼ·ψ(ξᵢ-ξⱼ)
    --   Total = ∑∑ conj(cᵢ)cⱼ·(ψ(ξᵢ-ξⱼ) - ψ(ξᵢ) - conj(ψ(ξⱼ)))
    -- Build extended vectors: ξ' = (0, ξ₁, ..., ξₙ), c' = (-∑cᵢ, c₁, ..., cₙ)
    set ξ' : Fin (n + 1) → G := Fin.cons 0 ξ
    set c' : Fin (n + 1) → ℂ := Fin.cons (-∑ i, c i) c
    -- c' sums to zero
    have hc'_sum : ∑ i, c' i = 0 := by
      simp only [c', Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      ring
    -- Apply conditionally positive definite to get .re ≥ 0 for the (n+1)-point sum
    have hcpd := hψ_cpd.re_nonneg (n + 1) ξ' c' hc'_sum
    -- Show the (n+1)-point sum equals our kernel sum
    suffices heq : (∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
        starRingEnd ℂ (c' a) * c' b * ψ (ξ' a - ξ' b)).re =
      (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        (ψ (ξ i - ξ j) - ψ (ξ i) - starRingEnd ℂ (ψ (ξ j)))).re by
      linarith
    -- The (n+1)-point conditionally positive definite sum = our kernel sum. Prove by direct algebraic manipulation.
    -- Key: ∑_{a,b:Fin(n+1)} conj(c'_a) * c'_b * ψ(ξ'_a - ξ'_b)
    --     = ∑_{i,j:Fin n} conj(c_i) * c_j * (ψ(ξ_i - ξ_j) - ψ(ξ_i) - conj(ψ(ξ_j)))
    -- Split the (n+1)-sum into head + tail for both indices.
    have key : ∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
        starRingEnd ℂ (c' a) * c' b * ψ (ξ' a - ξ' b) =
      ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        (ψ (ξ i - ξ j) - ψ (ξ i) - starRingEnd ℂ (ψ (ξ j))) := by
      -- Split outer and inner sums at index 0
      simp_rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, c', ξ']
      -- Expand and simplify using ψ(0) = 0, ψ(-x) = conj(ψ(x))
      simp only [sub_zero, hψ_zero, mul_zero, zero_add]
      -- Goal shape (from trace_state):
      -- ∑ x, conj(-∑c) * c x * ψ(0 - ξ x) +
      --   ∑ x, ((conj(c x) * (-∑c)) * ψ(ξ x) + ∑ j, conj(c x) * c j * ψ(ξ x - ξ j))
      -- = ∑ i, ∑ j, conj(c i) * c j * (ψ(ξ i - ξ j) - ψ(ξ i) - conj(ψ(ξ j)))
      -- Step 1: Replace ψ(0 - ξ x) → ψ(-ξ x) → conj(ψ(ξ x))
      simp_rw [show ∀ x, (0 : G) - ξ x = -(ξ x) from fun x => by simp, hψ_herm]
      -- Step 2: Factor conj(-∑c) = -conj(∑c) and distribute into double sums
      -- The LHS has three components after expansion:
      -- T1 = ∑_j conj(-∑c) * c_j * conj(ψ(ξ_j)) = -(∑_i conj(c_i)) * ∑_j c_j * conj(ψ(ξ_j))
      -- T2 = ∑_i (conj(c_i) * (-∑c)) * ψ(ξ_i) = -∑_i conj(c_i) * (∑_j c_j) * ψ(ξ_i)
      -- T3 = ∑_i ∑_j conj(c_i) * c_j * ψ(ξ_i - ξ_j)
      -- We need T1 + T2 + T3 = ∑∑ conj(c_i)*c_j*(ψ(ξ_i-ξ_j) - ψ(ξ_i) - conj(ψ(ξ_j)))
      -- Proof: factor T1 = -∑∑ conj(c_i)*c_j*conj(ψ(ξ_j))
      --        factor T2 = -∑∑ conj(c_i)*c_j*ψ(ξ_i)
      --        then T3 - T2' - T1' = ∑∑ conj(c_i)*c_j*(ψ(ξ_i-ξ_j) - ψ(ξ_i) - conj(ψ(ξ_j)))
      -- Use transitivity through the double sum form
      have hT1 : ∑ x, (starRingEnd ℂ) (-∑ i, c i) * c x * (starRingEnd ℂ) (ψ (ξ x)) =
          -(∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * (starRingEnd ℂ) (ψ (ξ j))) := by
        simp_rw [map_neg, _root_.map_sum, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
        rw [Finset.sum_comm]
      have hT2 : ∀ x, ((starRingEnd ℂ) (c x) * -∑ i, c i) * ψ (ξ x) =
          -(∑ j, (starRingEnd ℂ) (c x) * c j * ψ (ξ x)) := by
        intro x; ring_nf
        congr 1
        rw [show (starRingEnd ℂ) (c x) * (∑ i, c i) * ψ (ξ x) =
          (starRingEnd ℂ) (c x) * ψ (ξ x) * ∑ i, c i from by ring]
        rw [Finset.mul_sum]
      rw [hT1]; simp_rw [hT2]
      -- Goal: -∑∑ conj(c_i)*c_j*conj(ψ(ξ_j)) + ∑_x(-∑_j ... + ∑_j ...) = ∑∑ conj(c_i)*c_j*(...)
      simp_rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [key]
  · -- .im = 0: kernel K_{ij} is Hermitian so the quadratic form is real
    -- K_{ij} = ψ(ξᵢ-ξⱼ) - ψ(ξᵢ) - conj(ψ(ξⱼ))
    -- conj(K_{ji}) = conj(ψ(ξⱼ-ξᵢ)) - conj(ψ(ξⱼ)) - ψ(ξᵢ) = ψ(ξᵢ-ξⱼ) - conj(ψ(ξⱼ)) - ψ(ξᵢ) = K_{ij}
    have hK_herm : ∀ i j : Fin n,
        starRingEnd ℂ (ψ (ξ i - ξ j) - ψ (ξ i) - starRingEnd ℂ (ψ (ξ j))) =
        ψ (ξ j - ξ i) - ψ (ξ j) - starRingEnd ℂ (ψ (ξ i)) := by
      intro i j
      simp only [map_sub, starRingEnd_self_apply]
      -- Goal: conj(ψ(ξᵢ-ξⱼ)) - conj(ψ(ξᵢ)) - ψ(ξⱼ) = ψ(ξⱼ-ξᵢ) - ψ(ξⱼ) - conj(ψ(ξᵢ))
      -- Use hψ_herm: conj(ψ(a)) = ψ(-a)
      rw [← hψ_herm (ξ i - ξ j), neg_sub]
      ring
    -- conj(∑∑ conj(cᵢ)cⱼ Kᵢⱼ) = ∑∑ conj(cⱼ)cᵢ Kⱼᵢ [swap conj inside] = ∑∑ conj(cᵢ)cⱼ Kᵢⱼ [swap i↔j]
    have hself_conj : starRingEnd ℂ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        (ψ (ξ i - ξ j) - ψ (ξ i) - starRingEnd ℂ (ψ (ξ j)))) =
      ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        (ψ (ξ i - ξ j) - ψ (ξ i) - starRingEnd ℂ (ψ (ξ j))) := by
      simp only [_root_.map_sum, map_mul, starRingEnd_self_apply, hK_herm]
      -- Goal: ∑_i ∑_j c_i * conj(c_j) * K_{ji} = ∑_i ∑_j conj(c_i) * c_j * K_{ij}
      -- Swap i ↔ j in the LHS using Finset.sum_comm for the outer pair
      rw [Finset.sum_comm]
      congr 1; ext i; congr 1; ext j; ring
    -- z = conj(z) implies z.im = 0
    have h := congr_arg Complex.im hself_conj
    simp only [Complex.conj_im, neg_eq_iff_eq_neg] at h
    linarith

-- Entrywise products of positive-definite kernels are positive definite,
-- by Mathlib's matrix Schur product theorem.
open Matrix in
private lemma pd_kernel_to_posSemidef {n : ℕ} {K : Fin n → Fin n → ℂ}
    (hK : ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * K i j) :
    (Matrix.of K).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun c => ?_⟩
  · -- Hermitianness: conj(K j i) = K i j
    -- From hK: the quadratic form's .im = 0 for all c. This means the sum
    -- equals its conjugate. Swapping i↔j in the conjugate gives
    -- ∑∑ conj(cᵢ)cⱼ conj(Kⱼᵢ) = ∑∑ conj(cᵢ)cⱼ Kᵢⱼ for all c, forcing conj(K j i) = K i j.
    -- Step 1: for all c, the sum equals its conjugate (since .im = 0)
    have hself_conj : ∀ c : Fin n → ℂ,
        starRingEnd ℂ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * K i j) =
        ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * K i j := by
      intro c
      have h0 := hK c
      rw [Complex.nonneg_iff] at h0
      rw [Complex.conj_eq_iff_im]
      exact h0.2.symm
    -- Step 2: conjugating and swapping indices gives ∑∑ conj(cᵢ)cⱼ conj(Kⱼᵢ) = ∑∑ conj(cᵢ)cⱼ Kᵢⱼ
    have hswap : ∀ c : Fin n → ℂ,
        ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * starRingEnd ℂ (K j i) =
        ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * K i j := by
      intro c
      have h := hself_conj c
      simp only [_root_.map_sum, map_mul, starRingEnd_self_apply] at h
      -- h : ∑ i, ∑ j, c i * conj(c j) * conj(K i j) = ∑ i, ∑ j, conj(c i) * c j * K i j
      rw [Finset.sum_comm] at h
      -- h : ∑ j, ∑ i, c i * conj(c j) * conj(K i j) = ...
      -- Rename i↔j: ∑ i, ∑ j, c j * conj(c i) * conj(K j i) = ...
      -- = ∑ i, ∑ j, conj(c i) * c j * conj(K j i)
      have := h
      simp_rw [show ∀ i j : Fin n, c j * (starRingEnd ℂ) (c i) * (starRingEnd ℂ) (K j i) =
        (starRingEnd ℂ) (c i) * c j * (starRingEnd ℂ) (K j i) from fun i j => by ring] at this
      exact this
    -- Step 3: pointwise extraction via Pi.single
    -- hdiff_zero : ∀ c, ∑∑ conj(cₐ)cᵦ (Kₐᵦ - conj(Kᵦₐ)) = 0
    have hdiff_zero : ∀ c : Fin n → ℂ,
        ∑ a, ∑ b, starRingEnd ℂ (c a) * c b * (K a b - starRingEnd ℂ (K b a)) = 0 := by
      intro c
      have h := hswap c
      have : ∑ a, ∑ b, starRingEnd ℂ (c a) * c b * (K a b - starRingEnd ℂ (K b a)) =
          (∑ a, ∑ b, starRingEnd ℂ (c a) * c b * K a b) -
          (∑ a, ∑ b, starRingEnd ℂ (c a) * c b * starRingEnd ℂ (K b a)) := by
        simp_rw [mul_sub, ← Finset.sum_sub_distrib]
      rw [this, h, _root_.sub_self]
    -- For c = Pi.single a 1: sum collapses to D a a = 0
    have hD_diag : ∀ a : Fin n, K a a - starRingEnd ℂ (K a a) = 0 := by
      intro a
      have := hdiff_zero (Pi.single a 1)
      simp only [Pi.single_apply, apply_ite (starRingEnd ℂ), map_one, map_zero, ite_mul,
        one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true] at this
      exact this
    -- For off-diagonal: use two test vectors
    -- hdiff_single : ∀ a b c_a c_b, sum at (Pi.single a c_a + Pi.single b c_b)
    -- We need: ∀ a b, K a b = conj(K b a)
    ext i j
    simp only [conjTranspose_apply, of_apply, star_def]
    -- Goal: conj(K j i) = K i j, i.e., K i j - conj(K j i) = 0 → conj(K j i) = K i j
    -- Equivalently: K j i - conj(K i j) = 0 (swapped), then take conj
    -- Actually we want conj(K j i) = K i j, which is K i j = conj(K j i),
    -- i.e., K i j - conj(K j i) = 0
    -- Step: prove ∀ a b, K a b - conj(K b a) = 0
    suffices hD : ∀ a b : Fin n, K a b - starRingEnd ℂ (K b a) = 0 by
      have := hD i j; rw [sub_eq_zero] at this; exact this.symm
    intro a b
    by_cases hab : a = b
    · subst hab; exact hD_diag a
    · -- Use two-point test vectors to show D(a,b) = K(a,b) - conj(K(b,a)) = 0
      -- Helper: simplify sums at 2-entry vectors using sum_ite_eq'
      have heval : ∀ s t : ℂ,
          starRingEnd ℂ s * s * (K a a - starRingEnd ℂ (K a a)) +
          starRingEnd ℂ s * t * (K a b - starRingEnd ℂ (K b a)) +
          (starRingEnd ℂ t * s * (K b a - starRingEnd ℂ (K a b)) +
          starRingEnd ℂ t * t * (K b b - starRingEnd ℂ (K b b))) = 0 := by
        intro s t
        have key := hdiff_zero (fun k => (if k = a then s else 0) + (if k = b then t else 0))
        simp only [map_add, apply_ite (starRingEnd ℂ), map_zero, add_mul, mul_add,
          ite_mul, mul_ite, mul_zero, zero_mul, Finset.sum_add_distrib,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true] at key
        convert key using 1
        ring
      -- Specialize: D(a,a) = D(b,b) = 0 simplifies the evaluation
      have hDa := hD_diag a
      have hDb := hD_diag b
      -- Test 1: s = 1, t = 1 gives D(a,b) + D(b,a) = 0
      have htest1 := heval 1 1
      simp only [map_one, one_mul, hDa, hDb, mul_zero, zero_add, add_zero] at htest1
      -- htest1 : (K a b - conj(K b a)) + (K b a - conj(K a b)) = 0
      -- Test 2: s = 1, t = I gives I·D(a,b) + (-I)·D(b,a) = 0
      have htest2 := heval 1 I
      simp only [map_one, one_mul, mul_one, conj_I, hDa, hDb, mul_zero, zero_add,
        add_zero] at htest2
      set D₁ := K a b - starRingEnd ℂ (K b a)
      set D₂ := K b a - starRingEnd ℂ (K a b)
      have h_sum : D₁ + D₂ = 0 := htest1
      -- htest2 : I * D₁ + (-I) * D₂ = 0 (or with extra 1)
      -- Strategy: D₁ + D₂ = 0 and I*D₁ - I*D₂ = 0 → D₁ = D₂, then 2D₁ = 0.
      have h_eq : D₁ = D₂ := by
        have h_Idiff : I * D₁ - I * D₂ = 0 := by
          have := htest2
          -- htest2 might have form: I * D₁ + -I * D₂ = 0
          -- Need: I * D₁ - I * D₂ = 0
          -- -I * D₂ = -(I * D₂), so I*D₁ + (-I)*D₂ = I*D₁ - I*D₂
          linear_combination this
        have : I * (D₁ - D₂) = 0 := by rw [mul_sub]; exact h_Idiff
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left I_ne_zero)
      -- D₁ = D₂ and D₁ + D₂ = 0 → 2D₁ = 0
      have : D₁ + D₁ = 0 := by rw [show D₁ + D₁ = D₁ + D₂ from by rw [h_eq]]; exact h_sum
      rw [show D₁ = (2 : ℂ)⁻¹ * (D₁ + D₁) from by ring, this, mul_zero]
  · change 0 ≤ dotProduct (star c) (mulVec (Matrix.of K) c)
    have key : dotProduct (star c) (mulVec (Matrix.of K) c) =
        ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * K i j := by
      simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def]
      congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j; ring
    rw [key]; exact hK c

private lemma pd_kernel_mul
    {n : ℕ} {M N : Fin n → Fin n → ℂ}
    (hM : ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * M i j)
    (hN : ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * N i j) :
    ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (M i j * N i j) := by
  open Matrix in
  intro c
  have hMN : ((Matrix.of M).hadamard (Matrix.of N)).PosSemidef :=
    (pd_kernel_to_posSemidef hM).hadamard (pd_kernel_to_posSemidef hN)
  have hquad := hMN.dotProduct_mulVec_nonneg c
  have hquad_eq : dotProduct (star c)
      (mulVec ((Matrix.of M).hadamard (Matrix.of N)) c) =
      ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (M i j * N i j) := by
    simp only [dotProduct, mulVec, Matrix.hadamard_apply, Matrix.of_apply,
      Pi.star_apply, RCLike.star_def]
    congr 1
    ext i
    rw [Finset.mul_sum]
    congr 1
    ext j
    ring
  rw [← hquad_eq]
  exact hquad

-- Entrywise k-th power of PD kernel is PD (by iterated Schur product).
private lemma pd_kernel_pow
    {n : ℕ} {M : Fin n → Fin n → ℂ}
    (hM : ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * M i j)
    (k : ℕ) :
    ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * M i j ^ k := by
  induction k with
  | zero =>
    intro c; simp only [pow_zero, mul_one]
    -- ∑∑ conj(cᵢ)cⱼ = |∑cᵢ|² ≥ 0
    -- Factor: ∑_i ∑_j conj(c_i) * c_j = (∑ conj(c_i)) * (∑ c_j) = conj(∑ c_i) * ∑ c_j
    rw [show ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j =
        starRingEnd ℂ (∑ i, c i) * ∑ j, c j from by
      rw [_root_.map_sum]; simp_rw [Finset.sum_mul, Finset.mul_sum]]
    exact star_mul_self_nonneg _
  | succ k ih =>
    intro c
    have hpow : ∀ i j : Fin n, M i j ^ (k + 1) = M i j ^ k * M i j :=
      fun i j => pow_succ (M i j) k
    simp_rw [hpow]
    exact pd_kernel_mul ih hM c

-- Helper: entrywise exp of PD kernel is PD.
-- Proof: (1 + tM/N)^N → exp(tM) entrywise as N → ∞.
-- Each (1 + tM/N)^N is PD (by pd_kernel_pow + the base case 1 + tM/N is PD).
private lemma exp_pd_kernel
    {n : ℕ} {M : Fin n → Fin n → ℂ}
    (hM : ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * M i j)
    (t : ℝ) (ht : 0 ≤ t) :
    ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * exp (↑t * M i j) := by
  intro c
  -- For large N, define K_N(i,j) = (1 + t·M(i,j)/N)^N
  -- Step 1: K_N is PD for large N
  -- 1 + t·M(i,j)/N is PD when N > t·‖M‖:
  --   ∑∑ conj(cᵢ)cⱼ (1 + (t/N)·Mᵢⱼ) = |∑cᵢ|² + (t/N)·∑∑ conj(cᵢ)cⱼ Mᵢⱼ ≥ 0
  -- Then (1 + tM/N)^N is PD by pd_kernel_pow.
  have hbase : ∀ᶠ N : ℕ in Filter.atTop,
      ∀ d : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (d i) * d j *
        (1 + ↑t / (↑N : ℂ) * M i j) := by
    filter_upwards [Filter.Ici_mem_atTop 1] with N (hN : 1 ≤ N)
    intro d
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have htN : 0 ≤ t / N := div_nonneg ht (le_of_lt hN_pos)
    -- ∑∑ conj(cᵢ)dⱼ(1 + (t/N)Mᵢⱼ) = |∑dᵢ|² + (t/N)·∑∑ conj(cᵢ)dⱼ Mᵢⱼ
    -- Split: ∑∑ conj(cᵢ)dⱼ(1 + (t/N)Mᵢⱼ) = ∑∑ conj(cᵢ)dⱼ + (t/N)·∑∑ conj(cᵢ)dⱼ Mᵢⱼ
    have hsplit : ∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (d i) * d j * (1 + ↑t / (↑N : ℂ) * M i j) =
      ∑ i, ∑ j, starRingEnd ℂ (d i) * d j +
        (↑t / ↑N : ℂ) * ∑ i, ∑ j, starRingEnd ℂ (d i) * d j * M i j := by
      trans ∑ i : Fin n, (∑ j, starRingEnd ℂ (d i) * d j +
        ↑t / ↑N * ∑ j, starRingEnd ℂ (d i) * d j * M i j)
      · congr 1; ext i
        trans ∑ j : Fin n, (starRingEnd ℂ (d i) * d j +
          ↑t / ↑N * (starRingEnd ℂ (d i) * d j * M i j))
        · congr 1; ext j; ring
        · rw [Finset.sum_add_distrib, Finset.mul_sum]
      · rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsplit]
    apply add_nonneg
    · -- |∑dᵢ|² ≥ 0
      rw [show ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (d i) * d j =
          starRingEnd ℂ (∑ i, d i) * ∑ j, d j from by
        rw [_root_.map_sum]; simp_rw [Finset.sum_mul, Finset.mul_sum]]
      exact star_mul_self_nonneg _
    · -- (t/N) · (PD sum) ≥ 0
      have hcoeff : (0 : ℂ) ≤ ↑t / ↑N := by
        rw [Complex.nonneg_iff]; constructor
        · simp; exact div_nonneg ht (le_of_lt hN_pos)
        · simp
      exact mul_nonneg hcoeff (hM d)
  -- Step 2: K_N = (1 + tM/N)^N is PD
  have hpow_pd : ∀ᶠ N : ℕ in Filter.atTop,
      ∀ d : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (d i) * d j *
        (1 + ↑t / (↑N : ℂ) * M i j) ^ N := by
    filter_upwards [hbase] with N hN
    intro d
    have hpow_eq : ∀ i j, (1 + ↑t / (↑N : ℂ) * M i j) ^ N =
        (fun i j => 1 + ↑t / (↑N : ℂ) * M i j) i j ^ N := fun i j => rfl
    simp_rw [hpow_eq]
    exact pd_kernel_pow hN N d
  -- Step 3: pointwise convergence (1 + tMᵢⱼ/N)^N → exp(tMᵢⱼ)
  have hlim : ∀ i j : Fin n, Filter.Tendsto
      (fun N : ℕ => starRingEnd ℂ (c i) * c j * (1 + ↑t / (↑N : ℂ) * M i j) ^ N)
      Filter.atTop (nhds (starRingEnd ℂ (c i) * c j * exp (↑t * M i j))) := by
    intro i j
    apply Filter.Tendsto.const_mul
    exact (Complex.tendsto_one_add_div_pow_exp (↑t * M i j)).congr fun N => by
      by_cases hN : (N : ℕ) = 0
      · simp [hN]
      · have hNne : (↑N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
        congr 1; field_simp
  -- Step 4: sum convergence (finite sum + pointwise → sum converges)
  have hsum_lim : Filter.Tendsto
      (fun N : ℕ => ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j *
        (1 + ↑t / (↑N : ℂ) * M i j) ^ N)
      Filter.atTop
      (nhds (∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j * exp (↑t * M i j))) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => hlim i j
  -- Step 5: limit of nonneg is nonneg
  exact ge_of_tendsto hsum_lim (by filter_upwards [hpow_pd] with N hN; exact hN c)

namespace IsConditionallyPositiveDefinite

private theorem schoenberg_exp_of_zero
    {G : Type*} [AddGroup G] {ψ : G → ℂ}
    (hψ_cpd : IsConditionallyPositiveDefinite ψ) (hψ_zero : ψ 0 = 0)
    (hψ_herm : ∀ ξ, ψ (-ξ) = starRingEnd ℂ (ψ ξ))
    (t : ℝ) (ht : 0 ≤ t) :
    IsPositiveDefinite (fun ξ => exp (↑t * ψ ξ)) := by
  intro n x c
  -- The kernel M_{ij} = ψ(x_i - x_j) - ψ(x_i) - conj(ψ(x_j)) is PD
  have hM := fun d => cpd_kernel_pd hψ_cpd hψ_zero hψ_herm n x d
  -- exp(tM) is PD
  have hexpM := exp_pd_kernel hM t ht
  -- Factorization: exp(t·ψ(x_i-x_j)) = exp(t·ψ(x_i))·exp(t·conj(ψ(x_j)))·exp(t·M_{ij})
  -- Use d_i = c_i · exp(t · conj(ψ(x_i))) so conj(d_i) = conj(c_i) · exp(t · ψ(x_i))
  set d : Fin n → ℂ := fun i => c i * exp (↑t * starRingEnd ℂ (ψ (x i)))
  suffices hsuff : ∀ i j : Fin n,
      starRingEnd ℂ (c i) * c j * exp (↑t * ψ (x i - x j)) =
      starRingEnd ℂ (d i) * d j *
        exp (↑t * (ψ (x i - x j) - ψ (x i) - starRingEnd ℂ (ψ (x j)))) by
    simp_rw [hsuff]
    exact hexpM d
  intro i j
  simp only [d, map_mul]
  -- conj(exp(t * conj(ψ(x i)))) = exp(conj(t * conj(ψ(x i)))) = exp(t * ψ(x i))
  rw [show starRingEnd ℂ (exp (↑t * starRingEnd ℂ (ψ (x i)))) =
      exp (↑t * ψ (x i)) from by
    rw [← Complex.exp_conj]; congr 1
    simp [Complex.conj_ofReal]]
  -- Now: conj(c i) * exp(t*ψ(x i)) * (c j * exp(t*conj(ψ(x j)))) * exp(t*M_ij)
  --    = conj(c i) * c j * exp(t*ψ(x i - x j))
  rw [show starRingEnd ℂ (c i) * exp (↑t * ψ (x i)) *
      (c j * exp (↑t * starRingEnd ℂ (ψ (x j)))) *
      exp (↑t * (ψ (x i - x j) - ψ (x i) - starRingEnd ℂ (ψ (x j)))) =
    starRingEnd ℂ (c i) * c j *
      (exp (↑t * ψ (x i)) * exp (↑t * starRingEnd ℂ (ψ (x j))) *
        exp (↑t * (ψ (x i - x j) - ψ (x i) - starRingEnd ℂ (ψ (x j))))) from by ring]
  congr 1
  rw [← exp_add, ← exp_add]
  congr 1; ring

/-- **Schoenberg's theorem.** If `ψ : G → ℂ` is conditionally positive definite
and Hermitian, then `x ↦ exp (t * ψ x)` is positive definite for every `t ≥ 0`.
This algebraic statement assumes no topology or continuity.

The group correspondence is stated by A. S. Holevo, “Conditionally Positive Definite
Functions in Quantum Probability,” *Proceedings of the International Congress of
Mathematicians* (Berkeley, 1986), vol. 2, pp. 1011–1020, Introduction, opening paragraph.
The proceedings scan is available at
<https://sites.math.rutgers.edu/~zeilberg/akherim/icm1986.pdf>.

Our conditionally positive definite convention requires the zero-sum quadratic form
itself to be real and nonnegative. -/
theorem schoenberg_exp
    {G : Type*} [AddGroup G] {ψ : G → ℂ}
    (hψ_cpd : IsConditionallyPositiveDefinite ψ)
    (hψ_herm : ∀ ξ, ψ (-ξ) = starRingEnd ℂ (ψ ξ))
    (t : ℝ) (ht : 0 ≤ t) :
    IsPositiveDefinite (fun ξ => exp (↑t * ψ ξ)) := by
  let ψ₀ := ψ 0
  let ψ' : G → ℂ := fun x => ψ x - ψ₀
  have hψ₀_conj : starRingEnd ℂ ψ₀ = ψ₀ := by
    simpa [ψ₀] using (hψ_herm (0 : G)).symm
  have hψ₀_im : ψ₀.im = 0 := Complex.conj_eq_iff_im.mp hψ₀_conj
  have hψ₀_real : ψ₀ = (ψ₀.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hψ₀_im]
  have hψ'_cpd : IsConditionallyPositiveDefinite ψ' := by
    simpa [ψ', sub_eq_add_neg] using
      hψ_cpd.add (IsConditionallyPositiveDefinite.const (G := G) (-ψ₀))
  have hψ'_zero : ψ' 0 = 0 := by simp [ψ', ψ₀]
  have hψ'_herm : ∀ ξ, ψ' (-ξ) = starRingEnd ℂ (ψ' ξ) := by
    intro ξ
    calc
      ψ' (-ξ) = starRingEnd ℂ (ψ ξ) - ψ₀ := by simp [ψ', hψ_herm ξ]
      _ = starRingEnd ℂ (ψ ξ - ψ₀) := by rw [map_sub, hψ₀_conj]
  have hnormalized := schoenberg_exp_of_zero hψ'_cpd hψ'_zero hψ'_herm t ht
  let a : ℝ := Real.exp (t * ψ₀.re)
  have ha : 0 ≤ a := le_of_lt (Real.exp_pos _)
  have hfactor : exp ((↑t : ℂ) * ψ₀) = (a : ℂ) := by
    rw [hψ₀_real, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  have hexp : ∀ ξ, exp ((↑t : ℂ) * ψ ξ) =
      (a : ℂ) * exp ((↑t : ℂ) * ψ' ξ) := by
    intro ξ
    have hdecomp : ψ ξ = ψ₀ + ψ' ξ := by simp [ψ']
    rw [hdecomp, mul_add, Complex.exp_add, hfactor]
  simpa only [hexp] using hnormalized.smul_nonneg ha

end IsConditionallyPositiveDefinite

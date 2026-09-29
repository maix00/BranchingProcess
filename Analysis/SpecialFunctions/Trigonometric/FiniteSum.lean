module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Algebra.BigOperators.Field

public section

open scoped BigOperators

/-!
# Finite trigonometric sums

This file records finite trigonometric sum identities that do not depend on
probability or spectral terminology.
-/

namespace Real

/-- Orthogonality normalization of a nonconstant discrete Dirichlet sine mode.
For `0 < k < L`, the squared sine values at the `L - 1` interior grid
points sum to `L / 2`. -/
theorem sum_sin_sq_mul_pi_div (L k : ℕ) (hkpos : 0 < k) (hklt : k < L) :
    (∑ j ∈ Finset.range (L - 1),
      sin (Real.pi * (k : ℝ) / (L : ℝ) * ((j + 1 : ℕ) : ℝ)) ^ 2) =
      (L : ℝ) / 2 := by
  let θ : ℝ := Real.pi * (k : ℝ) / (L : ℝ)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hkpos.trans hklt
  have hθpos : 0 < θ := by
    dsimp [θ]
    positivity
  have hθlt : θ < Real.pi := by
    dsimp [θ]
    rw [div_lt_iff₀ hLpos]
    nlinarith [pi_pos, (show (k : ℝ) < L by exact_mod_cast hklt)]
  have hsinθ : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθpos hθlt
  have hLθ : (L : ℝ) * θ = (k : ℝ) * Real.pi := by
    dsimp [θ]
    field_simp
  have hLm1θ : ((L - 1 : ℕ) : ℝ) * θ = (k : ℝ) * Real.pi - θ := by
    calc
      ((L - 1 : ℕ) : ℝ) * θ = ((L : ℝ) - 1) * θ := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2
          (Nat.ne_of_gt (hkpos.trans hklt)))]
        norm_num
      _ = (L : ℝ) * θ - θ := by ring
      _ = _ := by rw [hLθ]
  have hLm2 : (((L - 1 : ℕ) : ℝ) - 1) * (2 * θ) / 2 + 2 * θ =
      (k : ℝ) * Real.pi := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt (hkpos.trans hklt)))]
    nlinarith [hLθ]
  have hhalf : (2 * θ) / 2 = θ := by ring
  have hs := sin_mul_sum_cos (L - 1) (2 * θ) (2 * θ)
  rw [hhalf, show ((L - 1 : ℕ) : ℝ) * (2 * θ) / 2 =
      ((L - 1 : ℕ) : ℝ) * θ by ring, hLm1θ,
      Real.sin_nat_mul_pi_sub θ k, hLm2, Real.cos_nat_mul_pi] at hs
  have hsign : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by
    rw [← pow_add]
    simp [← two_mul]
  have hcosSum : (∑ j ∈ Finset.range (L - 1),
      cos (2 * θ * (j : ℝ) + 2 * θ)) = -1 := by
    apply mul_left_cancel₀ hsinθ.ne'
    calc
      sin θ * (∑ j ∈ Finset.range (L - 1), cos (2 * θ * (j : ℝ) + 2 * θ))
          = -sin θ := by nlinarith [hs, hsign]
      _ = sin θ * (-1) := by ring
  simp_rw [show Real.pi * (k : ℝ) / (L : ℝ) = θ by rfl]
  simp_rw [Real.sin_sq_eq_half_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hcosSum' :
      (∑ j ∈ Finset.range (L - 1), cos (2 * (θ * ((j + 1 : ℕ) : ℝ)))) = -1 := by
    calc
      _ = ∑ j ∈ Finset.range (L - 1), cos (2 * θ * (j : ℝ) + 2 * θ) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        push_cast
        ring
      _ = -1 := hcosSum
  rw [← Finset.sum_div, hcosSum']
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt (hkpos.trans hklt)))]
  ring

/-- Successor-width form of `Real.sum_sin_sq_mul_pi_div`, indexed directly
by the number of interior grid points. -/
theorem sum_sin_sq_mul_pi_div_succ (interiorCount k : ℕ)
    (hkpos : 0 < k) (hklt : k < interiorCount + 1) :
    (∑ j ∈ Finset.range interiorCount,
      sin (Real.pi * (k : ℝ) / ((interiorCount + 1 : ℕ) : ℝ) *
        ((j + 1 : ℕ) : ℝ)) ^ 2) =
      ((interiorCount + 1 : ℕ) : ℝ) / 2 := by
  simpa only [Nat.add_sub_cancel] using
    sum_sin_sq_mul_pi_div (interiorCount + 1) k hkpos hklt

end Real

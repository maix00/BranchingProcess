/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

/-!
# Bounds for finite geometric sums

Elementary bounds for finite geometric progressions.
-/

open scoped BigOperators

namespace Finset

/-- A finite geometric progression beginning at exponent one is bounded by
the corresponding infinite progression. -/
theorem sum_range_pow_succ_le_div_one_sub {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (n : ℕ) :
    (∑ i ∈ range n, r ^ (i + 1)) ≤ r / (1 - r) := by
  have hsum : (∑ i ∈ range n, r ^ (i + 1)) =
      r * ((r ^ n - 1) / (r - 1)) := by
    calc
      (∑ i ∈ range n, r ^ (i + 1)) = (∑ i ∈ range n, r ^ i) * r := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [pow_succ]
      _ = r * ((r ^ n - 1) / (r - 1)) := by
        rw [geom_sum_eq (ne_of_lt hr₁) n]
        ring
  have hrewrite : r * ((r ^ n - 1) / (r - 1)) =
      r * (1 - r ^ n) / (1 - r) := by
    rw [show r ^ n - 1 = -(1 - r ^ n) by ring,
      show r - 1 = -(1 - r) by ring, neg_div_neg_eq]
    ring
  have hden : 0 < 1 - r := sub_pos.mpr hr₁
  rw [hsum, hrewrite]
  apply (div_le_div_iff₀ hden hden).2
  nlinarith [mul_nonneg hr₀ (pow_nonneg hr₀ n)]

/-- After removing the first term, a finite geometric progression is bounded
by the tail of the corresponding infinite progression. -/
theorem sum_range_pow_succ_sub_first_le_sq_div_one_sub {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (n : ℕ) :
    (∑ i ∈ range n, r ^ (i + 1)) - r ≤ r ^ 2 / (1 - r) := by
  have hsum := sum_range_pow_succ_le_div_one_sub hr₀ hr₁ n
  have hden : 0 < 1 - r := sub_pos.mpr hr₁
  calc
    (∑ i ∈ range n, r ^ (i + 1)) - r ≤ r / (1 - r) - r :=
      sub_le_sub_right hsum r
    _ = r ^ 2 / (1 - r) := by
      field_simp [hden.ne']
      ring

end Finset

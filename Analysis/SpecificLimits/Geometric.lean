module

public import Mathlib.Analysis.SpecificLimits.Normed

public section

/-!
# Bounds for finite geometric sums

Elementary comparisons between finite geometric progressions and their
convergent infinite sums.
-/

open scoped BigOperators Topology

namespace Finset

/-- A finite geometric progression beginning at exponent one is bounded by
the corresponding infinite progression. -/
theorem sum_range_pow_succ_le_div_one_sub {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (n : ℕ) :
    (∑ i ∈ range n, r ^ (i + 1)) ≤ r / (1 - r) := by
  have hsum : Summable (fun i : ℕ => r ^ (i + 1)) := by
    simpa [pow_succ', mul_comm] using
      (summable_geometric_of_lt_one hr₀ hr₁).mul_left r
  calc
    (∑ i ∈ range n, r ^ (i + 1)) ≤ ∑' i : ℕ, r ^ (i + 1) :=
      hsum.sum_le_tsum (range n) (fun i _ => pow_nonneg hr₀ _)
    _ = r * ∑' i : ℕ, r ^ i := by
      rw [← tsum_mul_left]
      congr with i
      rw [pow_succ]
      ac_rfl
    _ = r / (1 - r) := by
      rw [tsum_geometric_of_lt_one hr₀ hr₁]
      simp [div_eq_mul_inv]

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

module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

/-!
# Bounds for weighted finite sums

If nonnegative masses are multiplied by weights in a fixed interval, the
weighted sum bounds the unweighted total after scaling by the interval ends.
-/

open scoped BigOperators

@[expose] public section

namespace Finset

/-- Lower and upper bounds on nonnegative weights bound the weighted sum by
the corresponding multiples of the total mass. -/
theorem weightedSum_bounds_of_sum_eq
    {ι : Type*} (s : Finset ι) (mass weight : ι → ℝ)
    (lower upper weighted : ℝ)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hlower : ∀ i ∈ s, lower ≤ weight i)
    (hupper : ∀ i ∈ s, weight i ≤ upper)
    (hweighted : ∑ i ∈ s, mass i * weight i = weighted) :
    lower * ∑ i ∈ s, mass i ≤ weighted ∧
      weighted ≤ upper * ∑ i ∈ s, mass i := by
  constructor
  · rw [← hweighted, Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => by
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left (hlower i hi) (hmass i hi)
  · rw [← hweighted, Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => by
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left (hupper i hi) (hmass i hi)

/-- A positive upper weight bound turns a weighted sum into a lower bound on
the total mass. -/
theorem div_le_sum_of_weightedSum_eq
    {ι : Type*} (s : Finset ι) (mass weight : ι → ℝ)
    (upper weighted : ℝ) (hupper_pos : 0 < upper)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hweight : ∀ i ∈ s, weight i ≤ upper)
    (hweighted : ∑ i ∈ s, mass i * weight i = weighted) :
    weighted / upper ≤ ∑ i ∈ s, mass i := by
  have hbound : weighted ≤ upper * ∑ i ∈ s, mass i := by
    rw [← hweighted, Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => by
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left (hweight i hi) (hmass i hi)
  exact (div_le_iff₀ hupper_pos).2 (by simpa [mul_comm] using hbound)

/-- A positive lower weight bound turns a weighted sum into an upper bound on
the total mass. -/
theorem sum_le_div_of_weightedSum_eq
    {ι : Type*} (s : Finset ι) (mass weight : ι → ℝ)
    (lower weighted : ℝ) (hlower_pos : 0 < lower)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hweight : ∀ i ∈ s, lower ≤ weight i)
    (hweighted : ∑ i ∈ s, mass i * weight i = weighted) :
    (∑ i ∈ s, mass i) ≤ weighted / lower := by
  have hbound : lower * ∑ i ∈ s, mass i ≤ weighted := by
    rw [← hweighted, Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => by
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left (hweight i hi) (hmass i hi)
  exact (le_div_iff₀ hlower_pos).2 (by simpa [mul_comm] using hbound)

end Finset

end

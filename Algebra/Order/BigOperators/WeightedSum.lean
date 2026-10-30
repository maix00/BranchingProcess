/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Bounds for weighted finite sums

## Public declarations

For a finite set $s$ in an ordered field, nonnegative masses $m_i$, weights
$w_i$, and weighted sum $W=\sum_{i\in s}m_iw_i$, the results below compare
$W$ with the total mass. The first result requires only an ordered ring.

- `weightedSum_bounds_of_sum_eq`: for nonnegative masses $m_i$ and weights
  $\ell\le w_i\le u$ on $s$, if
  $\sum_{i\in s}m_iw_i=W$, then
  $\ell\sum_{i\in s}m_i\le W\le u\sum_{i\in s}m_i$.
- `div_le_sum_of_weightedSum_eq`: for nonnegative masses $m_i$, if
  $w_i\le u$ on $s$ with $u>0$ and $\sum_{i\in s}m_iw_i=W$, then
  $W/u\le\sum_{i\in s}m_i$.
- `sum_le_div_of_weightedSum_eq`: for nonnegative masses $m_i$, if
  $0<\ell\le w_i$ on $s$ and $\sum_{i\in s}m_iw_i=W$, then
  $\sum_{i\in s}m_i\le W/\ell$.

If nonnegative masses are multiplied by weights in a fixed interval, the
weighted sum bounds the unweighted total after scaling by the interval ends.
-/

open scoped BigOperators

@[expose] public section

namespace Finset

/-- Lower and upper bounds on nonnegative weights bound the weighted sum by
the corresponding multiples of the total mass. -/
theorem weightedSum_bounds_of_sum_eq
    {ι : Type*} {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]
    (s : Finset ι)
    (mass weight : ι → R) (lower upper weighted : R)
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
    {ι : Type*} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (s : Finset ι)
    (mass weight : ι → R) (upper weighted : R) (hupper_pos : 0 < upper)
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
    {ι : Type*} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (s : Finset ι)
    (mass weight : ι → R) (lower weighted : R) (hlower_pos : 0 < lower)
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

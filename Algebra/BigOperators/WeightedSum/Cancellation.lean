/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Ring.Finset

import Mathlib.Tactic.FieldSimp

/-!
# Algebra of normalized finite weighted sums

For a finite family of weights in a field with nonzero total weight, the
unnormalized sum can be recovered from its normalized weighted average. These
identities use only finite sums and field operations; probability and
size-biased measure applications belong in their own modules.

## Public declarations

For `Z = ∑ i ∈ s, w i ≠ 0`, `normalized_weight_sum_eq_one` states
`∑ i ∈ s, w i / Z = 1`. `weighted_sum_eq_normalized_average` rewrites
`∑ i ∈ s, w i * g i` as
`Z * ∑ i ∈ s, (w i / Z) * g i`. If also every `w i` is nonzero,
`sum_eq_normalized_weighted_sum` gives
`∑ i ∈ s, g i = Z * ∑ i ∈ s, (w i / Z) * (g i / w i)`.
-/

@[expose] public section

open scoped BigOperators

namespace Finset

variable {ι : Type*}
variable {R : Type*} [Field R]

/-- A nonzero finite weight normalizer gives normalized weights of total mass
one. -/
theorem normalized_weight_sum_eq_one (s : Finset ι) (w : ι → R)
    (hZ : (∑ i ∈ s, w i) ≠ 0) :
    ∑ i ∈ s, w i / (∑ j ∈ s, w j) = 1 := by
  rw [← Finset.sum_div]
  exact div_self hZ

/-- A weighted sum is its normalizer times the normalized weighted average. -/
theorem weighted_sum_eq_normalized_average (s : Finset ι) (w g : ι → R)
    (hZ : (∑ i ∈ s, w i) ≠ 0) :
    (∑ i ∈ s, w i * g i) =
      (∑ i ∈ s, w i) *
        ∑ i ∈ s, (w i / (∑ j ∈ s, w j)) * g i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [hZ]

/-- Cancellation of nonzero weights inside a normalized weighted average. -/
theorem sum_eq_normalized_weighted_sum (s : Finset ι) (w g : ι → R)
    (hZ : (∑ i ∈ s, w i) ≠ 0)
    (hw : ∀ i ∈ s, w i ≠ 0) :
    (∑ i ∈ s, g i) =
      (∑ i ∈ s, w i) *
        ∑ i ∈ s, (w i / (∑ j ∈ s, w j)) * (g i / w i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [hZ, hw i hi]

end Finset

end

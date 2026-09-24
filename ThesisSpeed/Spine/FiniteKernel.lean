import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Finite offspring size bias: the algebraic one-step identity

The full many-to-one formula also needs a random offspring point process,
integration, independence across generations, and induction. This file proves
only the finite one-step normalization and cancellation used in that proof.
It does not assert the probabilistic many-to-one formula.

Reference for the induction to be formalized: Zhan Shi, *Branching Random
Walks*, Section 1.3, Theorem 1.1.
-/

namespace ThesisSpeed.Spine

variable {ι : Type*}

/-- Normalizing finite positive weights gives total mass one. -/
theorem normalized_kernel_sum (s : Finset ι) (w : ι → ℝ)
    (hZ : (∑ i ∈ s, w i) ≠ 0) :
    ∑ i ∈ s, w i / (∑ j ∈ s, w j) = 1 := by
  rw [← Finset.sum_div]
  exact div_self hZ

/-- The weighted direction of the finite one-generation formula. -/
theorem weighted_sum_as_kernel (s : Finset ι) (w g : ι → ℝ)
    (hZ : (∑ i ∈ s, w i) ≠ 0) :
    (∑ i ∈ s, w i * g i) =
      (∑ i ∈ s, w i) *
        ∑ i ∈ s, (w i / (∑ j ∈ s, w j)) * g i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [hZ]

/-- The one-generation size-bias cancellation, with arbitrary nonzero
weights. For the thesis, `w i = exp (-λ * Ξᵢ)`; the random and countable
offspring extension is a separate obligation. -/
theorem weighted_sum_cancel (s : Finset ι) (w g : ι → ℝ)
    (hZ : (∑ i ∈ s, w i) ≠ 0)
    (hw : ∀ i ∈ s, w i ≠ 0) :
    (∑ i ∈ s, g i) =
      (∑ i ∈ s, w i) *
        ∑ i ∈ s, (w i / (∑ j ∈ s, w j)) * (g i / w i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [hZ, hw i hi]

end ThesisSpeed.Spine

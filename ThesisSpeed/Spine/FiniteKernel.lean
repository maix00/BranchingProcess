import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Exp

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
weights. For the thesis, `w i = exp (-lam * Ξᵢ)`; the random and countable
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

/- The exponential specialization is the exact algebraic form used by the
spine change of measure.  It records explicitly that no positivity assumption
on the displacement is needed: exponential weights are always nonzero. -/
theorem weighted_sum_cancel_exp {s : Finset ι} (lam : ℝ) (ξ g : ι → ℝ)
    (hZ : (∑ i ∈ s, Real.exp (-lam * ξ i)) ≠ 0) :
    (∑ i ∈ s, g i) =
      (∑ i ∈ s, Real.exp (-lam * ξ i)) *
        ∑ i ∈ s,
          (Real.exp (-lam * ξ i) /
            (∑ j ∈ s, Real.exp (-lam * ξ j))) *
            (g i / Real.exp (-lam * ξ i)) := by
  apply weighted_sum_cancel s (fun i => Real.exp (-lam * ξ i)) g hZ
  intro i hi
  exact ne_of_gt (Real.exp_pos _)

/-- A nonempty finite offspring family has a strictly positive exponential
normalizer, so the side condition in `weighted_sum_cancel_exp` is automatic. -/
theorem exp_weight_sum_ne_zero {s : Finset ι} (lam : ℝ) (ξ : ι → ℝ)
    (hs : s.Nonempty) :
    (∑ i ∈ s, Real.exp (-lam * ξ i)) ≠ 0 := by
  have hpos : 0 < ∑ i ∈ s, Real.exp (-lam * ξ i) := by
    exact Finset.sum_pos' (fun i hi => le_of_lt (Real.exp_pos _))
      (by
        obtain ⟨i, hi⟩ := hs
        exact ⟨i, hi, Real.exp_pos _⟩)
  exact ne_of_gt hpos

end ThesisSpeed.Spine

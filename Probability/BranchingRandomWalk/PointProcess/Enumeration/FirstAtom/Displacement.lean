import Probability.BranchingRandomWalk.PointProcess.Enumeration.FirstAtom.Weight

/-!
# Displacement of the leftmost realized child

Measurability of the selected displacement, its minimality among realized
children, and its agreement with slot zero on the ordered support used by the
selected walk.
-/

open MeasureTheory
open scoped Topology BigOperators ENNReal NNReal

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory


/-- The displacement of the leftmost realized child is measurable even
before restricting to the finite-weight event. -/
noncomputable def firstAtomDisplacement (ξ : NatRealStep) : ℝ :=
  value' ξ (firstAtomIndex ξ)

theorem firstAtomDisplacement_measurable :
    Measurable firstAtomDisplacement := by
  have h : Measurable
      (fun p : ℕ × NatRealStep => value' p.2 p.1) :=
    measurable_from_prod_countable_right
      (fun i => value'_measurable i)
  exact h.comp (firstAtomIndex_measurable.prodMk measurable_id)

theorem firstAtomDisplacement_le_of_finite_weight
    (ξ : NatRealStep)
    (hsum : totalChildWeight ξ ≠ ∞)
    (hnonempty : ∃ j, ξ ∈ childRealized j)
    (i : ℕ) (hi : ξ ∈ childRealized i) :
    firstAtomDisplacement ξ ≤ value' ξ i :=
  (firstAtomIndex_spec_of_finite_weight ξ hsum hnonempty).2.1 i hi

/-- On the ordered support already used by the selected walk, the new
measurable first-atom selector agrees with slot zero. -/
theorem firstAtomIndex_eq_zero_of_ordered (ξ : NatRealStep)
    (hξ : ξ ∈ orderedSteps) (hzero : ξ ∈ childRealized 0) :
    firstAtomIndex ξ = 0 := by
  apply firstAtomIndex_eq_of_firstAtomAt
  refine ⟨hzero, ?_, ?_⟩
  · intro j hj
    exact orderedSteps_value_mono ξ hξ (Nat.zero_le j) hj
  · intro j hj
    omega

theorem firstAtomDisplacement_eq_first_of_ordered (ξ : NatRealStep)
    (hξ : ξ ∈ orderedSteps) (hzero : ξ ∈ childRealized 0) :
    firstAtomDisplacement ξ = value' ξ 0 := by
  simp [firstAtomDisplacement,
    firstAtomIndex_eq_zero_of_ordered ξ hξ hzero,
    value']

end ProbabilityTheory.BranchingRandomWalk

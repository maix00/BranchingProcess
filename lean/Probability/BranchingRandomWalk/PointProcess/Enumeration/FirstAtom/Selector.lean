import MeasureTheory.Measure.AtomFiniteness
import MeasureTheory.BranchingWalk.Step.Slot
import MeasureTheory.BranchingWalk.Cloud.Order.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The leftmost realized child slot

The raw mark guarantees a child in slot zero but leaves the remaining slots
unordered. This layer selects the leftmost realized slot and resolves position
ties by the smaller raw slot number. The selector is total; on marks with no
leftmost child it defaults to slot zero.
-/

open MeasureTheory
open scoped Topology BigOperators ENNReal NNReal

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory


/-- Slot `i` is the leftmost realized child; an equal-position tie is
resolved by the smaller raw slot number. -/
def firstAtomAt (ξ : NatRealStep) (i : ℕ) : Prop :=
  ξ ∈ childRealized i ∧
  (∀ j, ξ ∈ childRealized j →
    value ξ i ≤ value ξ j) ∧
  (∀ j, j < i → ξ ∈ childRealized j →
    value ξ i < value ξ j)

theorem firstAtomAt_measurable (i : ℕ) :
    MeasurableSet {ξ : NatRealStep | firstAtomAt ξ i} := by
  unfold firstAtomAt
  have hfirst : Measurable
      (fun ξ : NatRealStep => ξ ∈ childRealized i) :=
    (childRealized_measurable i).mem
  have hleast : Measurable
      (fun ξ : NatRealStep => ∀ j, ξ ∈ childRealized j →
        value ξ i ≤ value ξ j) := by
    apply Measurable.forall
    intro j
    exact (childRealized_measurable j).mem.imp
      ((measurableSet_le (value_measurable i)
        (value_measurable j)).mem)
  have htie : Measurable
      (fun ξ : NatRealStep => ∀ j, j < i → ξ ∈ childRealized j →
        value ξ i < value ξ j) := by
    apply Measurable.forall
    intro j
    exact measurable_const.imp
      ((childRealized_measurable j).mem.imp
        ((measurableSet_lt (value_measurable i)
          (value_measurable j)).mem))
  exact (hfirst.and (hleast.and htie)).setOf

/-- The tie rule makes the first-atom index unique. -/
theorem firstAtomAt_unique (ξ : NatRealStep) {i j : ℕ}
    (hi : firstAtomAt ξ i) (hj : firstAtomAt ξ j) : i = j := by
  rcases lt_trichotomy i j with hij | h | hji
  · have hlt := hj.2.2 i hij hi.1
    have hle := hi.2.1 j hj.1
    exact False.elim ((not_lt_of_ge hle) hlt)
  · exact h
  · have hlt := hi.2.2 j hji hj.1
    have hle := hj.2.1 i hi.1
    exact False.elim ((not_lt_of_ge hle) hlt)

/-- Left-local finiteness of the realized slots gives a first atom, even
when the raw slots themselves are not ordered. -/
theorem firstAtomAt_exists_of_finite_sublevels (ξ : NatRealStep)
    (hfinite : ∀ R : ℝ,
      {i : ℕ | ξ ∈ childRealized i ∧ value ξ i ≤ R}.Finite)
    (hnonempty : ∃ i, ξ ∈ childRealized i) :
    ∃ i, firstAtomAt ξ i := by
  classical
  obtain ⟨i₀, hi₀⟩ := hnonempty
  let s : Set ℕ :=
    {i | ξ ∈ childRealized i ∧
      value ξ i ≤ value ξ i₀}
  have hi₀s : i₀ ∈ s := ⟨hi₀, le_rfl⟩
  obtain ⟨j, hj⟩ :=
    (hfinite (value ξ i₀)).exists_minimalFor
      (value ξ) s ⟨i₀, hi₀s⟩
  have hmin : ∀ i, ξ ∈ childRealized i →
      value ξ j ≤ value ξ i := by
    intro i hi
    rcases le_total (value ξ j)
      (value ξ i) with h | h
    · exact h
    · have his : i ∈ s := ⟨hi, h.trans hj.1.2⟩
      exact hj.2 his h
  have hex : ∃ i : ℕ,
      ξ ∈ childRealized i ∧
      value ξ i = value ξ j :=
    ⟨j, hj.1.1, rfl⟩
  let k := Nat.find hex
  have hk : ξ ∈ childRealized k ∧
      value ξ k = value ξ j :=
    Nat.find_spec hex
  refine ⟨k, hk.1, ?_, ?_⟩
  · intro i hi
    rw [hk.2]
    exact hmin i hi
  · intro i hik hi
    have hle : value ξ k ≤ value ξ i := by
      rw [hk.2]
      exact hmin i hi
    have hne : value ξ k ≠ value ξ i := by
      intro heq
      have hki : k ≤ i := Nat.find_min' hex
        ⟨hi, by rw [← heq, hk.2]⟩
      omega
    exact lt_of_le_of_ne hle hne

/-- A total index selector. On empty marks or marks with no minimum it
defaults to slot zero; correctness statements therefore require nonemptiness. -/
noncomputable def firstAtomIndex (ξ : NatRealStep) : ℕ := by
  classical
  exact if h : ∃ i, firstAtomAt ξ i then Nat.find h else 0

theorem firstAtomIndex_spec (ξ : NatRealStep)
    (h : ∃ i, firstAtomAt ξ i) :
    firstAtomAt ξ (firstAtomIndex ξ) := by
  classical
  simp only [firstAtomIndex, dite_eq_left h]
  exact Nat.find_spec h

theorem firstAtomIndex_eq_of_firstAtomAt (ξ : NatRealStep) (i : ℕ)
    (hi : firstAtomAt ξ i) : firstAtomIndex ξ = i :=
  firstAtomAt_unique ξ (firstAtomIndex_spec ξ ⟨i, hi⟩) hi

/-- Choosing the leftmost realized raw slot uses only measurable comparisons
of countably many displacement coordinates. -/
theorem firstAtomIndex_measurable : Measurable firstAtomIndex := by
  classical
  apply measurable_to_countable'
  intro i
  let E : Set NatRealStep := {ξ | ∃ j, firstAtomAt ξ j}
  have hE : MeasurableSet E := by
    have hE' : E = ⋃ j : ℕ, {ξ | firstAtomAt ξ j} := by
      ext ξ
      simp [E]
    rw [hE']
    exact MeasurableSet.iUnion firstAtomAt_measurable
  by_cases hi : i = 0
  · subst i
    have heq : firstAtomIndex ⁻¹' {(0 : ℕ)} =
        Eᶜ ∪ {ξ | firstAtomAt ξ 0} := by
      ext ξ
      simp only [Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq]
      constructor
      · intro h
        by_cases hξ : ξ ∈ E
        · right
          have hs := firstAtomIndex_spec ξ hξ
          rwa [h] at hs
        · exact Or.inl hξ
      · rintro (hξ | hξ)
        · simp [firstAtomIndex, show ¬∃ j, firstAtomAt ξ j from hξ]
        · exact firstAtomIndex_eq_of_firstAtomAt ξ 0 hξ
    rw [heq]
    exact hE.compl.union (firstAtomAt_measurable 0)
  · have heq : firstAtomIndex ⁻¹' {i} =
        {ξ | firstAtomAt ξ i} := by
      ext ξ
      simp only [Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_ofPred_eq]
      constructor
      · intro h
        by_cases hξ : ξ ∈ E
        · have hs := firstAtomIndex_spec ξ hξ
          rwa [h] at hs
        · have hzero : firstAtomIndex ξ = 0 := by
            simp [firstAtomIndex, show ¬∃ j, firstAtomAt ξ j from hξ]
          exact False.elim (hi (h.symm.trans hzero))
      · exact firstAtomIndex_eq_of_firstAtomAt ξ i
    rw [heq]
    exact firstAtomAt_measurable i

end ProbabilityTheory.BranchingRandomWalk

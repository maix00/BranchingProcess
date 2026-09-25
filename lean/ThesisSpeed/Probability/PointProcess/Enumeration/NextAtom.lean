import ThesisSpeed.Probability.PointProcess.Enumeration.FirstAtom

/-!
# Measurable choice of the next offspring atom

A finite set of raw slots has already been used. The next selector returns
`none` when no realized unused child remains. This explicit terminal value is
needed when the point process has finitely many atoms.
-/

open MeasureTheory
open scoped Topology BigOperators ENNReal NNReal

namespace ThesisSpeed

/-- The optional natural-number slot has the discrete measurable structure:
every singleton, including `none`, is observable. -/
instance optionNatMeasurableSpace : MeasurableSpace (Option ℕ) := ⊤

/-- `i` is the first realized child outside `used`, in displacement order
with raw-slot tie breaking. -/
def nextAtomAt (ξ : OffspringMark) (used : Finset ℕ) (i : ℕ) : Prop :=
  ξ ∈ childRealized i ∧ i ∉ used ∧
  (∀ j, ξ ∈ childRealized j → j ∉ used →
    childDisplacement ξ i ≤ childDisplacement ξ j) ∧
  (∀ j, j < i → ξ ∈ childRealized j → j ∉ used →
    childDisplacement ξ i < childDisplacement ξ j)

theorem nextAtomAt_measurable (used : Finset ℕ) (i : ℕ) :
    MeasurableSet {ξ : OffspringMark | nextAtomAt ξ used i} := by
  unfold nextAtomAt
  have hreal : Measurable
      (fun ξ : OffspringMark => ξ ∈ childRealized i) :=
    (childRealized_measurable i).mem
  have hleast : Measurable
      (fun ξ : OffspringMark => ∀ j, ξ ∈ childRealized j → j ∉ used →
        childDisplacement ξ i ≤ childDisplacement ξ j) := by
    apply Measurable.forall
    intro j
    exact (childRealized_measurable j).mem.imp
      (measurable_const.imp
        ((measurableSet_le (childDisplacement_measurable i)
          (childDisplacement_measurable j)).mem))
  have htie : Measurable
      (fun ξ : OffspringMark => ∀ j, j < i → ξ ∈ childRealized j →
        j ∉ used → childDisplacement ξ i < childDisplacement ξ j) := by
    apply Measurable.forall
    intro j
    exact measurable_const.imp
      ((childRealized_measurable j).mem.imp
        (measurable_const.imp
          ((measurableSet_lt (childDisplacement_measurable i)
            (childDisplacement_measurable j)).mem)))
  exact (hreal.and (measurable_const.and (hleast.and htie))).setOf

theorem nextAtomAt_unique (ξ : OffspringMark) (used : Finset ℕ)
    {i j : ℕ} (hi : nextAtomAt ξ used i)
    (hj : nextAtomAt ξ used j) : i = j := by
  rcases lt_trichotomy i j with hij | h | hji
  · have hlt := hj.2.2.2 i hij hi.1 hi.2.1
    have hle := hi.2.2.1 j hj.1 hj.2.1
    exact False.elim ((not_lt_of_ge hle) hlt)
  · exact h
  · have hlt := hi.2.2.2 j hji hj.1 hj.2.1
    have hle := hj.2.2.1 i hi.1 hi.2.1
    exact False.elim ((not_lt_of_ge hle) hlt)

/-- There is a next atom whenever at least one realized slot remains and
the original point process is left-locally finite. -/
theorem nextAtomAt_exists_of_finite_sublevels
    (ξ : OffspringMark) (used : Finset ℕ)
    (hfinite : ∀ R : ℝ,
      {i : ℕ | ξ ∈ childRealized i ∧ childDisplacement ξ i ≤ R}.Finite)
    (havailable : ∃ i, ξ ∈ childRealized i ∧ i ∉ used) :
    ∃ i, nextAtomAt ξ used i := by
  classical
  obtain ⟨i₀, hi₀⟩ := havailable
  let s : Set ℕ := {i | ξ ∈ childRealized i ∧ i ∉ used ∧
    childDisplacement ξ i ≤ childDisplacement ξ i₀}
  have hsfinite : s.Finite :=
    (hfinite (childDisplacement ξ i₀)).subset (by
      intro i hi
      exact ⟨hi.1, hi.2.2⟩)
  have hi₀s : i₀ ∈ s := by
    exact ⟨hi₀.1, hi₀.2, le_rfl⟩
  obtain ⟨j, hj⟩ :=
    hsfinite.exists_minimalFor (childDisplacement ξ) s ⟨i₀, hi₀s⟩
  have hmin : ∀ i, ξ ∈ childRealized i → i ∉ used →
      childDisplacement ξ j ≤ childDisplacement ξ i := by
    intro i hi hnot
    rcases le_total (childDisplacement ξ j)
      (childDisplacement ξ i) with h | h
    · exact h
    · have his : i ∈ s := ⟨hi, hnot, h.trans hj.1.2.2⟩
      exact hj.2 his h
  have hex : ∃ i : ℕ,
      ξ ∈ childRealized i ∧ i ∉ used ∧
      childDisplacement ξ i = childDisplacement ξ j :=
    ⟨j, hj.1.1, hj.1.2.1, rfl⟩
  let k := Nat.find hex
  have hk : ξ ∈ childRealized k ∧ k ∉ used ∧
      childDisplacement ξ k = childDisplacement ξ j :=
    Nat.find_spec hex
  refine ⟨k, hk.1, hk.2.1, ?_, ?_⟩
  · intro i hi hnot
    rw [hk.2.2]
    exact hmin i hi hnot
  · intro i hik hi hnot
    have hle : childDisplacement ξ k ≤ childDisplacement ξ i := by
      rw [hk.2.2]
      exact hmin i hi hnot
    have hne : childDisplacement ξ k ≠ childDisplacement ξ i := by
      intro heq
      have hki : k ≤ i := Nat.find_min' hex
        ⟨hi, hnot, by rw [← heq, hk.2.2]⟩
      omega
    exact lt_of_le_of_ne hle hne

/-- The next raw slot, or `none` if all realized slots have been used. -/
noncomputable def nextAtomIndex (used : Finset ℕ)
    (ξ : OffspringMark) : Option ℕ := by
  classical
  exact if h : ∃ i, nextAtomAt ξ used i then some (Nat.find h) else none

theorem nextAtomIndex_spec (ξ : OffspringMark) (used : Finset ℕ)
    (h : ∃ i, nextAtomAt ξ used i) :
    nextAtomAt ξ used ((nextAtomIndex used ξ).get (by
      classical
      simp [nextAtomIndex, h])) := by
  classical
  simp [nextAtomIndex, h]
  exact Nat.find_spec h

theorem nextAtomIndex_eq_some_iff (ξ : OffspringMark)
    (used : Finset ℕ) (i : ℕ) :
    nextAtomIndex used ξ = some i ↔ nextAtomAt ξ used i := by
  classical
  constructor
  · intro h
    by_cases he : ∃ j, nextAtomAt ξ used j
    · have hfind : Nat.find he = i := by
        simpa [nextAtomIndex, he] using h
      rw [← hfind]
      exact Nat.find_spec he
    · simp [nextAtomIndex, he] at h
  · intro hi
    have he : ∃ j, nextAtomAt ξ used j := ⟨i, hi⟩
    have hfind : Nat.find he = i :=
      nextAtomAt_unique ξ used (Nat.find_spec he) hi
    simp [nextAtomIndex, he, hfind]

theorem nextAtomIndex_eq_none_iff (ξ : OffspringMark)
    (used : Finset ℕ) :
    nextAtomIndex used ξ = none ↔
      ¬∃ i, nextAtomAt ξ used i := by
  classical
  by_cases he : ∃ i, nextAtomAt ξ used i <;>
    simp [nextAtomIndex, he]

theorem nextAtomIndex_eq_none_iff_of_finite_weight
    (ξ : OffspringMark) (used : Finset ℕ)
    (hsum : totalChildWeight ξ ≠ ∞) :
    nextAtomIndex used ξ = none ↔
      ¬∃ i, ξ ∈ childRealized i ∧ i ∉ used := by
  rw [nextAtomIndex_eq_none_iff]
  constructor
  · intro h havailable
    exact h (nextAtomAt_exists_of_finite_sublevels ξ used
      (finite_realized_children_below ξ hsum) havailable)
  · intro h ⟨i, hi⟩
    exact h ⟨i, hi.1, hi.2.1⟩

theorem nextAtomIndex_measurable (used : Finset ℕ) :
    Measurable (nextAtomIndex used) := by
  classical
  apply measurable_to_countable'
  intro o
  cases o with
  | none =>
      have hE : MeasurableSet
          {ξ : OffspringMark | ∃ i, nextAtomAt ξ used i} := by
        have heq : {ξ : OffspringMark | ∃ i, nextAtomAt ξ used i} =
            ⋃ i : ℕ, {ξ | nextAtomAt ξ used i} := by
          ext ξ
          simp
        rw [heq]
        exact MeasurableSet.iUnion (nextAtomAt_measurable used)
      have heq : nextAtomIndex used ⁻¹' {none} =
          {ξ : OffspringMark | ∃ i, nextAtomAt ξ used i}ᶜ := by
        ext ξ
        simpa using (nextAtomIndex_eq_none_iff ξ used)
      rw [heq]
      exact hE.compl
  | some i =>
      have heq : nextAtomIndex used ⁻¹' {some i} =
          {ξ : OffspringMark | nextAtomAt ξ used i} := by
        ext ξ
        simpa using (nextAtomIndex_eq_some_iff ξ used i)
      rw [heq]
      exact nextAtomAt_measurable used i

/-- The next-atom selector is jointly measurable in the mark and the
previously selected finite set. -/
theorem nextAtomIndex_joint_measurable :
    Measurable (fun p : Finset ℕ × OffspringMark =>
      nextAtomIndex p.1 p.2) :=
  measurable_from_prod_countable_right nextAtomIndex_measurable

end ThesisSpeed

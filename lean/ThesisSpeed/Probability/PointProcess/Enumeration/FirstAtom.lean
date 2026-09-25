import ThesisSpeed.Probability.PointProcess.LocalFiniteness
import ThesisSpeed.Probability.PointProcess.Enumeration.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# The first atom of an unsorted countable offspring mark

The raw mark has a guaranteed child in slot zero but does not order its
optional slots.  We select the leftmost realized slot, resolving position
ties by the original slot number.  The selector is measurable even on marks
without a leftmost child, where it defaults to zero.  Finite exponential
weight rules out that exceptional case.
-/

open MeasureTheory
open scoped Topology BigOperators ENNReal NNReal

namespace ThesisSpeed

/-- Slot `i` is the leftmost realized child; an equal-position tie is
resolved by the smaller raw slot number. -/
def firstAtomAt (ξ : OffspringMark) (i : ℕ) : Prop :=
  ξ ∈ childRealized i ∧
  (∀ j, ξ ∈ childRealized j →
    childDisplacement ξ i ≤ childDisplacement ξ j) ∧
  (∀ j, j < i → ξ ∈ childRealized j →
    childDisplacement ξ i < childDisplacement ξ j)

theorem firstAtomAt_measurable (i : ℕ) :
    MeasurableSet {ξ : OffspringMark | firstAtomAt ξ i} := by
  unfold firstAtomAt
  have hfirst : Measurable
      (fun ξ : OffspringMark => ξ ∈ childRealized i) :=
    (childRealized_measurable i).mem
  have hleast : Measurable
      (fun ξ : OffspringMark => ∀ j, ξ ∈ childRealized j →
        childDisplacement ξ i ≤ childDisplacement ξ j) := by
    apply Measurable.forall
    intro j
    exact (childRealized_measurable j).mem.imp
      ((measurableSet_le (childDisplacement_measurable i)
        (childDisplacement_measurable j)).mem)
  have htie : Measurable
      (fun ξ : OffspringMark => ∀ j, j < i → ξ ∈ childRealized j →
        childDisplacement ξ i < childDisplacement ξ j) := by
    apply Measurable.forall
    intro j
    exact measurable_const.imp
      ((childRealized_measurable j).mem.imp
        ((measurableSet_lt (childDisplacement_measurable i)
          (childDisplacement_measurable j)).mem))
  exact (hfirst.and (hleast.and htie)).setOf

/-- The tie rule makes the first-atom index unique. -/
theorem firstAtomAt_unique (ξ : OffspringMark) {i j : ℕ}
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
theorem firstAtomAt_exists_of_finite_sublevels (ξ : OffspringMark)
    (hfinite : ∀ R : ℝ,
      {i : ℕ | ξ ∈ childRealized i ∧ childDisplacement ξ i ≤ R}.Finite)
    (hnonempty : ∃ i, ξ ∈ childRealized i) :
    ∃ i, firstAtomAt ξ i := by
  classical
  obtain ⟨i₀, hi₀⟩ := hnonempty
  let s : Set ℕ :=
    {i | ξ ∈ childRealized i ∧
      childDisplacement ξ i ≤ childDisplacement ξ i₀}
  have hi₀s : i₀ ∈ s := ⟨hi₀, le_rfl⟩
  obtain ⟨j, hj⟩ :=
    (hfinite (childDisplacement ξ i₀)).exists_minimalFor
      (childDisplacement ξ) s ⟨i₀, hi₀s⟩
  have hmin : ∀ i, ξ ∈ childRealized i →
      childDisplacement ξ j ≤ childDisplacement ξ i := by
    intro i hi
    rcases le_total (childDisplacement ξ j)
      (childDisplacement ξ i) with h | h
    · exact h
    · have his : i ∈ s := ⟨hi, h.trans hj.1.2⟩
      exact hj.2 his h
  have hex : ∃ i : ℕ,
      ξ ∈ childRealized i ∧
      childDisplacement ξ i = childDisplacement ξ j :=
    ⟨j, hj.1.1, rfl⟩
  let k := Nat.find hex
  have hk : ξ ∈ childRealized k ∧
      childDisplacement ξ k = childDisplacement ξ j :=
    Nat.find_spec hex
  refine ⟨k, hk.1, ?_, ?_⟩
  · intro i hi
    rw [hk.2]
    exact hmin i hi
  · intro i hik hi
    have hle : childDisplacement ξ k ≤ childDisplacement ξ i := by
      rw [hk.2]
      exact hmin i hi
    have hne : childDisplacement ξ k ≠ childDisplacement ξ i := by
      intro heq
      have hki : k ≤ i := Nat.find_min' hex
        ⟨hi, by rw [← heq, hk.2]⟩
      omega
    exact lt_of_le_of_ne hle hne

/-- A total index selector. On empty marks or marks with no minimum it
defaults to slot zero; correctness statements therefore require nonemptiness. -/
noncomputable def firstAtomIndex (ξ : OffspringMark) : ℕ := by
  classical
  exact if h : ∃ i, firstAtomAt ξ i then Nat.find h else 0

theorem firstAtomIndex_spec (ξ : OffspringMark)
    (h : ∃ i, firstAtomAt ξ i) :
    firstAtomAt ξ (firstAtomIndex ξ) := by
  classical
  simp only [firstAtomIndex, dite_eq_left h]
  exact Nat.find_spec h

theorem firstAtomIndex_eq_of_firstAtomAt (ξ : OffspringMark) (i : ℕ)
    (hi : firstAtomAt ξ i) : firstAtomIndex ξ = i :=
  firstAtomAt_unique ξ (firstAtomIndex_spec ξ ⟨i, hi⟩) hi

/-- Choosing the leftmost realized raw slot uses only measurable comparisons
of countably many displacement coordinates. -/
theorem firstAtomIndex_measurable : Measurable firstAtomIndex := by
  classical
  apply measurable_to_countable'
  intro i
  let E : Set OffspringMark := {ξ | ∃ j, firstAtomAt ξ j}
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

/-- Exponential weight of a realized raw child, with absent slots assigned
zero weight. -/
noncomputable def realizedChildWeight (ξ : OffspringMark) (i : ℕ) :
    ENNReal := by
  classical
  exact if ξ ∈ childRealized i then
    ENNReal.ofReal (Real.exp (-childDisplacement ξ i)) else 0

theorem realizedChildWeight_measurable (i : ℕ) :
    Measurable (fun ξ : OffspringMark => realizedChildWeight ξ i) := by
  classical
  unfold realizedChildWeight
  exact (ENNReal.measurable_ofReal.comp
    ((childDisplacement_measurable i).neg.exp)).ite
    (childRealized_measurable i) measurable_const

/-- The total exponential weight of every realized child. -/
noncomputable def totalChildWeight (ξ : OffspringMark) : ENNReal :=
  ∑' i, realizedChildWeight ξ i

theorem totalChildWeight_measurable : Measurable totalChildWeight := by
  unfold totalChildWeight
  exact Measurable.tsum realizedChildWeight_measurable

theorem finite_realized_children_below (ξ : OffspringMark)
    (hsum : (∑' i, realizedChildWeight ξ i) ≠ ∞)
    (R : ℝ) :
    {i : ℕ | ξ ∈ childRealized i ∧
      childDisplacement ξ i ≤ R}.Finite := by
  classical
  apply finite_atoms_of_weight_lower_bound
    (realizedChildWeight ξ) hsum _
    (ENNReal.ofReal (Real.exp (-R)))
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  intro i hi
  have hle := ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr (neg_le_neg hi.2))
  simpa [realizedChildWeight, hi.1] using hle

/-- A nonempty raw offspring mark has a genuine leftmost child under the
finite exponential-weight condition. -/
theorem firstAtomIndex_spec_of_finite_weight (ξ : OffspringMark)
    (hsum : totalChildWeight ξ ≠ ∞)
    (hnonempty : ∃ i, ξ ∈ childRealized i) :
    firstAtomAt ξ (firstAtomIndex ξ) :=
  firstAtomIndex_spec ξ
    (firstAtomAt_exists_of_finite_sublevels ξ
      (finite_realized_children_below ξ hsum) hnonempty)

/-- A finite first moment of total exponential offspring weight makes the
first-atom selector correct almost surely. The normalization
`E[totalChildWeight] = 1` is one instance of this hypothesis. -/
theorem firstAtomIndex_ae_firstAtomAt
    (μ : Measure OffspringMark)
    (hmoment : (∫⁻ ξ, totalChildWeight ξ ∂μ) ≠ ∞)
    (hnonempty : ∀ᵐ ξ ∂μ, ∃ i, ξ ∈ childRealized i) :
    ∀ᵐ ξ ∂μ, firstAtomAt ξ (firstAtomIndex ξ) := by
  filter_upwards [ae_lt_top totalChildWeight_measurable hmoment,
    hnonempty] with ξ hξ hne
  exact firstAtomIndex_spec_of_finite_weight ξ hξ.ne hne

/-- The displacement of the leftmost realized child is measurable even
before restricting to the finite-weight event. -/
noncomputable def firstAtomDisplacement (ξ : OffspringMark) : ℝ :=
  childDisplacement ξ (firstAtomIndex ξ)

theorem firstAtomDisplacement_measurable :
    Measurable firstAtomDisplacement := by
  have h : Measurable
      (fun p : ℕ × OffspringMark => childDisplacement p.2 p.1) :=
    measurable_from_prod_countable_right
      (fun i => childDisplacement_measurable i)
  exact h.comp (firstAtomIndex_measurable.prodMk measurable_id)

theorem firstAtomDisplacement_le_of_finite_weight
    (ξ : OffspringMark)
    (hsum : totalChildWeight ξ ≠ ∞)
    (hnonempty : ∃ j, ξ ∈ childRealized j)
    (i : ℕ) (hi : ξ ∈ childRealized i) :
    firstAtomDisplacement ξ ≤ childDisplacement ξ i :=
  (firstAtomIndex_spec_of_finite_weight ξ hsum hnonempty).2.1 i hi

/-- On the ordered support already used by the selected walk, the new
measurable first-atom selector agrees with slot zero. -/
theorem firstAtomIndex_eq_zero_of_ordered (ξ : OffspringMark)
    (hξ : ξ ∈ orderedOffspring) (hzero : ξ ∈ childRealized 0) :
    firstAtomIndex ξ = 0 := by
  apply firstAtomIndex_eq_of_firstAtomAt
  refine ⟨hzero, ?_, ?_⟩
  · intro j hj
    exact orderedOffspring_childDisplacement_mono ξ hξ (Nat.zero_le j) hj
  · intro j hj
    omega

theorem firstAtomDisplacement_eq_first_of_ordered (ξ : OffspringMark)
    (hξ : ξ ∈ orderedOffspring) (hzero : ξ ∈ childRealized 0) :
    firstAtomDisplacement ξ = firstDisplacement ξ := by
  simp [firstAtomDisplacement,
    firstAtomIndex_eq_zero_of_ordered ξ hξ hzero,
    childDisplacement, firstDisplacement]

end ThesisSpeed

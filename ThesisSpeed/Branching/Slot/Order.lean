import ThesisSpeed.Branching.Slot.Position

/-!
# Ordered child marks

The thesis writes `Ξ₁`, `Ξ₂`, ... for the successive optional children of a
parent, listed from the left. The ordering condition is the abstract
`OrderedBranchingStep`: the present slots form an initial segment and their
displacements do not decrease. Nothing in the condition refers to `ℝ`; this
file only records that it is measurable for the thesis's `ℕ`-indexed real
slots, and re-exports the two consequences used downstream.
-/

open MeasureTheory

namespace ThesisSpeed

/-- The child steps whose optional slots are enumerated from the left. -/
def orderedBranchingSteps : Set NatRealBranchingStep :=
  {ξ | OrderedBranchingStep ξ}

theorem mem_orderedBranchingSteps_iff (ξ : NatRealBranchingStep) :
    ξ ∈ orderedBranchingSteps ↔ OrderedBranchingStep ξ := Iff.rfl

/-- A condition on two slots that only forbids a later present slot before an
earlier absent one is measurable. -/
private theorem coord_none_measurable (i : ℕ) :
    MeasurableSet {ξ : NatRealBranchingStep | ξ i = none} := by
  rw [show {ξ : NatRealBranchingStep | ξ i = none} =
      (fun ξ : NatRealBranchingStep => ξ i) ⁻¹' ({none} : Set (Option ℝ)) from rfl]
  exact (measurable_pi_apply i) measurableSet_option_none

private theorem pairPrefix_measurable (i j : ℕ) :
    MeasurableSet {ξ : NatRealBranchingStep | ξ i = none → ξ j = none} := by
  have hi := coord_none_measurable i
  have hj := coord_none_measurable j
  rw [show {ξ : NatRealBranchingStep | ξ i = none → ξ j = none} =
      {ξ : NatRealBranchingStep | ξ i = none}ᶜ ∪
        {ξ : NatRealBranchingStep | ξ j = none} by
    ext ξ
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_union]
    tauto]
  exact hi.compl.union hj

/-- The pairwise monotonicity condition is measurable. The absent slot is split
off first, so the comparison only involves the measurable defaulted values. -/
private theorem pairOrdered_measurable (i j : ℕ) :
    MeasurableSet {ξ : NatRealBranchingStep |
      ∀ x y, ξ i = some x → ξ j = some y → x ≤ y} := by
  have hget : Measurable (fun o : Option ℝ => o.getD 0) := measurable_optionGetD 0
  have hnone_i := coord_none_measurable i
  have hnone_j := coord_none_measurable j
  have hle : MeasurableSet {ξ : NatRealBranchingStep |
      ((ξ i).getD 0) ≤ ((ξ j).getD 0)} :=
    measurableSet_le (hget.comp (measurable_pi_apply i))
      (hget.comp (measurable_pi_apply j))
  rw [show {ξ : NatRealBranchingStep |
        ∀ x y, ξ i = some x → ξ j = some y → x ≤ y} =
      {ξ : NatRealBranchingStep | ξ i = none} ∪
        ({ξ : NatRealBranchingStep | ξ j = none} ∪
          {ξ : NatRealBranchingStep | ((ξ i).getD 0) ≤ ((ξ j).getD 0)}) by
    ext ξ
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro h
      by_cases hi : ξ i = none
      · exact Or.inl hi
      · right
        by_cases hj : ξ j = none
        · exact Or.inl hj
        · right
          cases hx : ξ i with
          | none => exact absurd hx hi
          | some x =>
            cases hy : ξ j with
            | none => exact absurd hy hj
            | some y => simpa [hx, hy] using h x y hx hy
    · intro hmem x y hx hy
      rcases hmem with hi | hj | hle
      · simp [hi] at hx
      · simp [hj] at hy
      · simpa [hx, hy] using hle]
  exact hnone_i.union (hnone_j.union hle)

theorem orderedBranchingSteps_measurable : MeasurableSet orderedBranchingSteps := by
  have hset : orderedBranchingSteps = ⋂ i : ℕ, ⋂ j : ℕ,
      {ξ : NatRealBranchingStep |
        (i < j → ξ i = none → ξ j = none) ∧
        (i < j → ∀ x y, ξ i = some x → ξ j = some y → x ≤ y)} := by
    ext ξ
    simp only [orderedBranchingSteps, OrderedBranchingStep, branchingStepPresencePrefix,
      branchingStepPrefixOrdered, branchingStepPrefixRel, Set.mem_ofPred_eq,
      Set.mem_iInter]
    constructor
    · intro h
      intro i j
      exact ⟨fun hij => h.1 i j hij,
        fun hij x y hx hy => h.2 i j x y hij hx hy⟩
    · intro h
      exact ⟨fun i j hij => (h i j).1 hij,
        fun i j x y hij hx hy => (h i j).2 hij x y hx hy⟩
  rw [hset]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i < j
  · rw [show {ξ : NatRealBranchingStep |
          (i < j → ξ i = none → ξ j = none) ∧
          (i < j → ∀ x y, ξ i = some x → ξ j = some y → x ≤ y)} =
        {ξ : NatRealBranchingStep | ξ i = none → ξ j = none} ∩
        {ξ : NatRealBranchingStep |
          ∀ x y, ξ i = some x → ξ j = some y → x ≤ y} by
      ext ξ
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · intro h
        exact ⟨h.1 hij, h.2 hij⟩
      · intro h
        exact ⟨fun _ => h.1, fun _ => h.2⟩]
    exact (pairPrefix_measurable i j).inter (pairOrdered_measurable i j)
  · rw [show {ξ : NatRealBranchingStep |
          (i < j → ξ i = none → ξ j = none) ∧
          (i < j → ∀ x y, ξ i = some x → ξ j = some y → x ≤ y)} =
        Set.univ by
      ext ξ
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ⟨fun h => absurd h hij, fun h => absurd h hij⟩]
    exact MeasurableSet.univ

/-- Under the ordering condition a later present slot forces slot zero to be
present: the leftmost optional child exists whenever any child does. -/
theorem orderedBranchingSteps_first_present (ξ : NatRealBranchingStep)
    (hξ : ξ ∈ orderedBranchingSteps) (i : ℕ) (hi : ξ ∈ childPresent i) :
    ξ ∈ childPresent 0 :=
  branchingStep_present_of_le ξ hξ.1 (Nat.zero_le i) hi

/-- Optional child displacements are nondecreasing along the enumeration. -/
theorem orderedBranchingSteps_childDisplacement_mono (ξ : NatRealBranchingStep)
    (hξ : ξ ∈ orderedBranchingSteps) {i j : ℕ}
    (hij : i ≤ j) (hj : ξ ∈ childRealized j) :
    childDisplacement ξ i ≤ childDisplacement ξ j :=
  branchingStepIncrement_mono_of_present ξ hξ.2 hij
    (branchingStep_present_of_le ξ hξ.1 hij hj) hj

/-- The ambient mark space itself does not enforce the leftmost-slot rule. -/
def unorderedExample : NatRealBranchingStep :=
  fun i => if i = 0 then some 1 else if i = 1 then some 0 else none

theorem unorderedExample_not_ordered :
    unorderedExample ∉ orderedBranchingSteps := by
  intro h
  have hone : unorderedExample ∈ childPresent 1 := by
    simp [unorderedExample, childPresent, branchingStepPresent]
  have hle : childDisplacement unorderedExample 0 ≤
      childDisplacement unorderedExample 1 :=
    orderedBranchingSteps_childDisplacement_mono unorderedExample h
      (Nat.zero_le 1) hone
  norm_num [unorderedExample, childDisplacement, branchingStepIncrement] at hle

end ThesisSpeed

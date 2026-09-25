import ThesisSpeed.Probability.PointProcess.Legacy.PositionsWeighted

/-!
# Ordered offspring marks

The raw countable mark space permits arbitrary slot order. The thesis uses
`Ξ₁` and `Ξ₂` for the first and second leftmost children when they exist. These
are represented by slots zero and one only on the measurable subset below.
Empty offspring marks also belong to this subset. The support of an
offspring law on this subset is a separate hypothesis, not a consequence of
the product construction.
-/

open MeasureTheory

namespace ThesisSpeed

/-- Every realized child forces slot zero to be realized and lies no farther
left than it. The statement is vacuous for an empty offspring mark. -/
def firstIsLeftmost : Set WeightedBranchingStep :=
  {ξ | ∀ i, ξ ∈ childPresent i →
    ξ ∈ childPresent 0 ∧ (ξ 0).2 ≤ (ξ i).2}

/-- The optional realized slots form an initial segment. -/
def optionalSlotsInitial : Set WeightedBranchingStep :=
  {ξ | ∀ i, ξ ∈ childPresent (i + 1) → ξ ∈ childPresent i}

/-- Consecutive realized optional children are listed in position order. -/
def optionalDisplacementsOrdered : Set WeightedBranchingStep :=
  {ξ | ∀ i, ξ ∈ childPresent (i + 1) → (ξ i).2 ≤ (ξ (i + 1)).2}

/-- A measurable ordered enumeration of a nonempty countable offspring point
process, with ties resolved by slot number. -/
def orderedOffspring : Set WeightedBranchingStep :=
  firstIsLeftmost ∩ optionalSlotsInitial ∩ optionalDisplacementsOrdered

private theorem optionalDisplacement_measurable (i : ℕ) :
    Measurable (fun ξ : WeightedBranchingStep => (ξ i).2) :=
  (measurable_pi_apply i).snd

theorem firstIsLeftmost_measurable : MeasurableSet firstIsLeftmost := by
  have h : firstIsLeftmost =
      ⋂ i : ℕ, (childPresent i)ᶜ ∪
        (childPresent 0 ∩ {ξ : WeightedBranchingStep | (ξ 0).2 ≤ (ξ i).2}) := by
    ext ξ
    simp [firstIsLeftmost, Set.mem_iInter, imp_iff_not_or]
  rw [h]
  apply MeasurableSet.iInter
  intro i
  exact (childPresent_measurable i).compl.union
    ((childPresent_measurable 0).inter
      (measurableSet_le (optionalDisplacement_measurable 0)
        (optionalDisplacement_measurable i)))

theorem optionalSlotsInitial_measurable :
    MeasurableSet optionalSlotsInitial := by
  have h : optionalSlotsInitial =
      ⋂ i : ℕ, (childPresent (i + 1))ᶜ ∪ childPresent i := by
    ext ξ
    simp [optionalSlotsInitial, Set.mem_iInter, imp_iff_not_or]
  rw [h]
  exact MeasurableSet.iInter (fun i =>
    (childPresent_measurable (i + 1)).compl.union
      (childPresent_measurable i))

theorem optionalDisplacementsOrdered_measurable :
    MeasurableSet optionalDisplacementsOrdered := by
  have h : optionalDisplacementsOrdered =
      ⋂ i : ℕ, (childPresent (i + 1))ᶜ ∪
        {ξ : WeightedBranchingStep | (ξ i).2 ≤ (ξ (i + 1)).2} := by
    ext ξ
    simp [optionalDisplacementsOrdered, Set.mem_iInter, imp_iff_not_or]
  rw [h]
  apply MeasurableSet.iInter
  intro i
  exact (childPresent_measurable (i + 1)).compl.union
    (measurableSet_le (optionalDisplacement_measurable i)
      (optionalDisplacement_measurable (i + 1)))

theorem orderedOffspring_measurable : MeasurableSet orderedOffspring :=
  (firstIsLeftmost_measurable.inter optionalSlotsInitial_measurable).inter
    optionalDisplacementsOrdered_measurable

theorem orderedOffspring_first_le (ξ : WeightedBranchingStep)
    (hξ : ξ ∈ orderedOffspring) (i : ℕ)
    (hi : ξ ∈ childPresent i) : (ξ 0).2 ≤ (ξ i).2 :=
  (hξ.1.1 i hi).2

theorem orderedOffspring_first_present (ξ : WeightedBranchingStep)
    (hξ : ξ ∈ orderedOffspring) (i : ℕ)
    (hi : ξ ∈ childPresent i) : ξ ∈ childPresent 0 :=
  (hξ.1.1 i hi).1

theorem orderedOffspring_second_present (ξ : WeightedBranchingStep)
    (hξ : ξ ∈ orderedOffspring) (i : ℕ)
    (hi : ξ ∈ childPresent (i + 1)) : ξ ∈ childPresent i :=
  hξ.1.2 i hi

theorem orderedOffspring_second_le_third (ξ : WeightedBranchingStep)
    (hξ : ξ ∈ orderedOffspring) (i : ℕ)
    (hi : ξ ∈ childPresent (i + 1)) :
    (ξ i).2 ≤ (ξ (i + 1)).2 :=
  hξ.2 i hi

/-- A later realized optional slot forces every earlier optional slot to
exist. This is the finite-prefix fact needed to truncate candidates at `N`. -/
theorem orderedOffspring_present_prefix (ξ : WeightedBranchingStep)
    (hξ : ξ ∈ orderedOffspring) :
    ∀ {i j : ℕ}, i ≤ j → ξ ∈ childPresent j → ξ ∈ childPresent i := by
  intro i j hij hj
  induction j generalizing i with
  | zero =>
      have hi : i = 0 := by omega
      simpa [hi] using hj
  | succ j ih =>
      by_cases hi : i = j + 1
      · simpa [hi] using hj
      · have hij' : i ≤ j := by omega
        exact ih hij' (orderedOffspring_second_present ξ hξ j hj)

/-- Optional child displacements are nondecreasing along the enumeration. -/
theorem orderedOffspring_displacement_mono (ξ : WeightedBranchingStep)
    (hξ : ξ ∈ orderedOffspring) :
    ∀ {i j : ℕ}, i ≤ j → ξ ∈ childPresent j →
      (ξ i).2 ≤ (ξ j).2 := by
  intro i j hij hj
  induction j generalizing i with
  | zero =>
      have hi : i = 0 := by omega
      simp [hi]
  | succ j ih =>
      by_cases hi : i = j + 1
      · simp [hi]
      · have hij' : i ≤ j := by omega
        have hjprev := orderedOffspring_second_present ξ hξ j hj
        exact (ih hij' hjprev).trans
          (orderedOffspring_second_le_third ξ hξ j hj)

theorem orderedOffspring_childRealized_prefix (ξ : WeightedBranchingStep)
    (hξ : ξ ∈ orderedOffspring) {i j : ℕ}
    (hij : i ≤ j) (hj : ξ ∈ childRealized j) :
    ξ ∈ childRealized i := by
  exact orderedOffspring_present_prefix ξ hξ hij hj

theorem orderedOffspring_childDisplacement_mono (ξ : WeightedBranchingStep)
    (hξ : ξ ∈ orderedOffspring) {i j : ℕ}
    (hij : i ≤ j) (hj : ξ ∈ childRealized j) :
    childDisplacement ξ i ≤ childDisplacement ξ j := by
  simpa [childDisplacement] using
    orderedOffspring_displacement_mono ξ hξ hij hj

/-- A child beyond slot `N-1` has `N` earlier realized children from the
same parent, each no farther to the right. -/
theorem orderedOffspring_truncation_witnesses (ξ : WeightedBranchingStep)
    (hξ : ξ ∈ orderedOffspring) (N j : ℕ)
    (hNj : N ≤ j) (hj : ξ ∈ childRealized j) :
    ∀ i < N, ξ ∈ childRealized i ∧
      childDisplacement ξ i ≤ childDisplacement ξ j := by
  intro i hi
  have hij : i ≤ j := by omega
  exact ⟨orderedOffspring_childRealized_prefix ξ hξ hij hj,
    orderedOffspring_childDisplacement_mono ξ hξ hij hj⟩

/-- The ambient mark space itself does not enforce the leftmost-slot rule. -/
def unorderedExample : WeightedBranchingStep :=
  fun i => if i = 0 then (1, 1) else if i = 1 then (1, 0) else (0, 0)

theorem unorderedExample_not_ordered :
    unorderedExample ∉ orderedOffspring := by
  intro h
  have hone : unorderedExample ∈ childPresent 1 := by
    norm_num [unorderedExample, childPresent]
  have hle := orderedOffspring_first_le unorderedExample h 1 hone
  norm_num [unorderedExample] at hle

end ThesisSpeed

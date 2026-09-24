import ThesisSpeed.Probability.Tree.OffspringMarks

/-!
# Ordered offspring marks

The raw countable mark space permits arbitrary slot order. The thesis uses
`Ξ₁` and `Ξ₂` for the first and second leftmost children. These are represented
by slots zero and one only on the measurable subset below. The support of an
offspring law on this subset is a separate hypothesis, not a consequence of
the product construction.
-/

open MeasureTheory

namespace ThesisSpeed

/-- Every optional realized child is at least as far right as slot zero. -/
def firstIsLeftmost : Set OffspringMark :=
  {ξ | ∀ i, ξ ∈ childPresent i → ξ.1 ≤ (ξ.2 i).2}

/-- The optional realized slots form an initial segment. -/
def optionalSlotsInitial : Set OffspringMark :=
  {ξ | ∀ i, ξ ∈ childPresent (i + 1) → ξ ∈ childPresent i}

/-- Consecutive realized optional children are listed in position order. -/
def optionalDisplacementsOrdered : Set OffspringMark :=
  {ξ | ∀ i, ξ ∈ childPresent (i + 1) → (ξ.2 i).2 ≤ (ξ.2 (i + 1)).2}

/-- A measurable ordered enumeration of a nonempty countable offspring point
process, with ties resolved by slot number. -/
def orderedOffspring : Set OffspringMark :=
  firstIsLeftmost ∩ optionalSlotsInitial ∩ optionalDisplacementsOrdered

private theorem optionalDisplacement_measurable (i : ℕ) :
    Measurable (fun ξ : OffspringMark => (ξ.2 i).2) :=
  ((measurable_pi_apply i).comp measurable_snd).snd

theorem firstIsLeftmost_measurable : MeasurableSet firstIsLeftmost := by
  have h : firstIsLeftmost =
      ⋂ i : ℕ, (childPresent i)ᶜ ∪
        {ξ : OffspringMark | ξ.1 ≤ (ξ.2 i).2} := by
    ext ξ
    simp [firstIsLeftmost, Set.mem_iInter, imp_iff_not_or]
  rw [h]
  apply MeasurableSet.iInter
  intro i
  exact (childPresent_measurable i).compl.union
    (measurableSet_le measurable_fst (optionalDisplacement_measurable i))

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
        {ξ : OffspringMark | (ξ.2 i).2 ≤ (ξ.2 (i + 1)).2} := by
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

theorem orderedOffspring_first_le (ξ : OffspringMark)
    (hξ : ξ ∈ orderedOffspring) (i : ℕ)
    (hi : ξ ∈ childPresent i) : ξ.1 ≤ (ξ.2 i).2 :=
  hξ.1.1 i hi

theorem orderedOffspring_second_present (ξ : OffspringMark)
    (hξ : ξ ∈ orderedOffspring) (i : ℕ)
    (hi : ξ ∈ childPresent (i + 1)) : ξ ∈ childPresent i :=
  hξ.1.2 i hi

theorem orderedOffspring_second_le_third (ξ : OffspringMark)
    (hξ : ξ ∈ orderedOffspring) (i : ℕ)
    (hi : ξ ∈ childPresent (i + 1)) :
    (ξ.2 i).2 ≤ (ξ.2 (i + 1)).2 :=
  hξ.2 i hi

/-- The ambient mark space itself does not enforce the leftmost-slot rule. -/
def unorderedExample : OffspringMark :=
  (1, fun i => if i = 0 then (1, 0) else (0, 0))

theorem unorderedExample_not_ordered :
    unorderedExample ∉ orderedOffspring := by
  intro h
  have hzero : unorderedExample ∈ childPresent 0 := by
    norm_num [unorderedExample, childPresent]
  have hle := orderedOffspring_first_le unorderedExample h 0 hzero
  norm_num [unorderedExample] at hle

end ThesisSpeed

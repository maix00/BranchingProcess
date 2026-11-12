/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Selection.Potential
public import Combinatorics.BranchingWalk.Step.Selection.Slot

/-!
# Selected continuation slot for a branching step

For a finite selection `R ξ`, the continuation rule chooses the second slot
when at least two are selected, the first slot when exactly one is selected,
and `⊥` when the selection is empty. In the selected-path construction, the
first selected child at a split starts a growth trial and this slot identifies
the second selected child that continues the path.

## Public declarations

- `Combinatorics.Branching.Step.FiniteSelection.selectedContinuationSlot R ξ` is
  defined by
  `\[\operatorname{selectedContinuationSlot}(R,\xi)=\begin{cases}
    \operatorname{secondSelectedSlot}(R,\xi),&2\le |R(\xi)|,\\
    \operatorname{firstSelectedSlot}(R,\xi),&0<|R(\xi)|<2,\\
    \bot,&|R(\xi)|=0.
  \end{cases}\]`.
- `Combinatorics.Branching.Step.FiniteSelection.selectedContinuationSlot_mem_of_selected_nonempty`
  proves that the continuation slot belongs to every nonempty selected family.
- `Combinatorics.Branching.Step.FiniteSelection.selectedContinuationSlot_eq_second_of_split`
  identifies it with the second selected slot when the family has at least
  two elements.
- `Combinatorics.Branching.Step.FiniteSelection.selectedContinuationSlot_eq_first_of_singleton`
  identifies it with the first selected slot when the family has cardinality
  one.
- `Combinatorics.Branching.Step.FiniteSelection.selectedContinuationSlot_eq_bot_of_selected_empty`
  gives its value on the empty family.
- `Combinatorics.Branching.Step.FiniteSelection.potentialValue'_selectedContinuationSlot_le_cutoff_add_firstSelectedSlotPositive`
  gives, after truncation by `reserveSelectionBelowPotential`,
  `\(\xi.potentialValue'(\varphi,
  selectedContinuationSlot(reserveSelectionBelowPotential(R,\varphi,M),\xi))
  \le M+firstSelectedSlotPositivePotential(R,\varphi,\xi)\)`.
-/

@[expose] public section

namespace Combinatorics.Branching

namespace Step.FiniteSelection

variable {α X : Type*}

attribute [local instance] Classical.propDecidable Classical.decEq

/-- At a split choose the second selected slot; for a singleton choose its
first slot, and use `⊥` when the selected family is empty. -/
noncomputable def selectedContinuationSlot [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X) : α :=
  if 2 ≤ (R ξ).card then secondSelectedSlot R ξ else
    if (R ξ).Nonempty then firstSelectedSlot R ξ else ⊥

theorem selectedContinuationSlot_mem_of_selected_nonempty [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hne : (R ξ).Nonempty) : selectedContinuationSlot R ξ ∈ R ξ := by
  by_cases hsplit : 2 ≤ (R ξ).card
  · simp [selectedContinuationSlot, hsplit]
    exact (secondSelectedSlot_mem_of_card R ξ hsplit).1
  · simp [selectedContinuationSlot, hsplit, hne]
    exact firstSelectedSlot_mem R ξ hne

theorem selectedContinuationSlot_eq_second_of_split [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hsplit : 2 ≤ (R ξ).card) :
    selectedContinuationSlot R ξ = secondSelectedSlot R ξ := by
  simp [selectedContinuationSlot, hsplit]

theorem selectedContinuationSlot_eq_first_of_singleton [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hsingleton : (R ξ).card = 1) :
    selectedContinuationSlot R ξ = firstSelectedSlot R ξ := by
  have htwo : ¬ 2 ≤ (R ξ).card := by omega
  have hne : (R ξ).Nonempty := Finset.card_pos.mp (by omega)
  simp [selectedContinuationSlot, htwo, hne]

/-- After potential truncation, the reserve slot has potential at most the
cutoff plus the positive potential of the original first selected slot. -/
theorem potentialValue'_selectedContinuationSlot_le_cutoff_add_firstSelectedSlotPositive
    [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : R.IsBoundedBy 2)
    (φ : Potential X) (M : ℝ) (hM : 0 ≤ M) (ξ : Step α X)
    (hordered : ξ.IsOrderedBy φ) (hne : (R ξ).Nonempty) :
    ξ.potentialValue' φ
      (selectedContinuationSlot (reserveSelectionBelowPotential R φ M) ξ) ≤
      M + firstSelectedSlotPositivePotential R φ ξ := by
  change ξ.potentialValue' φ
      (selectedContinuationSlot (reserveSelectionBelowPotential R φ M) ξ) ≤
        M + max 0 (ξ.potentialValue' φ (firstSelectedSlot R ξ))
  let S := reserveSelectionBelowPotential R φ M
  have hfirstR : firstSelectedSlot R ξ ∈ R ξ :=
    firstSelectedSlot_mem R ξ hne
  have hfirstOnly : firstSelectedSlot R ξ ∈ firstOnlySelectedChild R ξ := by
    rw [firstOnlySelectedChild, Step.FiniteSelection.mem_filter]
    exact ⟨hfirstR, rfl⟩
  have hfirstS : firstSelectedSlot R ξ ∈ S ξ := by
    change firstSelectedSlot R ξ ∈ reserveSelectionBelowPotential R φ M ξ
    rw [reserveSelectionBelowPotential]
    exact Finset.mem_union.mpr (Or.inl hfirstOnly)
  have hS_nonempty : (S ξ).Nonempty := ⟨firstSelectedSlot R ξ, hfirstS⟩
  by_cases hsplit : 2 ≤ (S ξ).card
  · rw [selectedContinuationSlot_eq_second_of_split S ξ hsplit]
    obtain ⟨_, hsecond⟩ :=
      reserveSelectionBelowPotential_edgePotentials_le_of_ordered
        R hR φ M ξ hordered hsplit
    exact hsecond.trans (le_add_of_nonneg_right (le_max_left 0
      (ξ.potentialValue' φ (firstSelectedSlot R ξ))))
  · have hcard : (S ξ).card = 1 := by
      have hpos : 0 < (S ξ).card := Finset.card_pos.mpr hS_nonempty
      omega
    rw [selectedContinuationSlot_eq_first_of_singleton S ξ hcard]
    have hfirstS_mem := firstSelectedSlot_mem S ξ hS_nonempty
    have hfirstEq : firstSelectedSlot S ξ = firstSelectedSlot R ξ := by
      by_contra hne'
      have htwo : 1 < (S ξ).card :=
        Finset.one_lt_card_iff.mpr
          ⟨firstSelectedSlot S ξ, firstSelectedSlot R ξ,
            hfirstS_mem, hfirstS, hne'⟩
      omega
    rw [hfirstEq]
    exact le_trans (le_max_right _ _) (le_add_of_nonneg_left hM)

@[simp] theorem selectedContinuationSlot_eq_bot_of_selected_empty
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hempty : R ξ = ∅) : selectedContinuationSlot R ξ = ⊥ := by
  simp [selectedContinuationSlot, hempty]

end Step.FiniteSelection

end Combinatorics.Branching

end

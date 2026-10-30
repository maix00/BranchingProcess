/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Selection.InfiniteOffspring.Batch

/-!
# Optional-slot population transitions

## Public declarations

These declarations belong to the variable-offspring selection model in
ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed.
infiniteOffspringTransition performs one rank-resetting leftmost-N
transition. infiniteSelectionStateNorm is the largest absolute particle
position. abs_position_le_infiniteSelectionStateNorm and
infiniteOffspringTransition_stateNorm_le bound particle positions and the
next-state norm by the sum of each parent's leftmost-child envelope.

infiniteOffspringTransition_mono and
infiniteOffspringFirstN_rank_monotone give the coordinatewise order
preservation of the transition and its ranked labels. The definitions
infinitePositionKeyShift and the results infiniteOffspringPositionKey_shift,
valueKey_add_const_lt_iff, rankBy_add_const, and isFirstNBy_add_const express
translation invariance of positions and ranks. infiniteOffspringTransition_shift
states that adding a common constant to all starting positions adds the same
constant after one transition.

Writing \(\|x\|_\infty=\max_{i<N}|x_i|\), the state bound is
\[
  \|T_b(x)\|_\infty
  \le \|x\|_\infty + \max_{i<N}|\mathrm{value}'(b_i,0)|.
\]
Under common offspring marks, \(x_i\le y_i\) for all i implies
\(T_b(x)_i\le T_b(y)_i\) for every i; translation covariance gives
\(T_b(x+c\mathbf 1)=T_b(x)+c\mathbf 1\).
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open scoped ENNReal

/-- The ranked state after one generation of an admissible countable-offspring
batch. -/
noncomputable def infiniteOffspringTransition
    {N : ℕ} (position : Fin N → ℝ) (offspring : Fin N → Step ℕ ℝ)
    (hgood : IsGoodInfiniteOffspringBatch offspring) : Fin N → ℝ :=
  fun i => infiniteOffspringPosition position offspring
    (selectedLabelAtRank (infiniteOffspringPosition position offspring)
      (infiniteOffspringFirstN position offspring hgood.finiteWeight)
      (infiniteOffspringFirstN_card position offspring hgood) i)

/-- The sup norm of a nonempty finite ranked population. -/
noncomputable def infiniteSelectionStateNorm {N : ℕ} (hN : 0 < N)
    (position : Fin N → ℝ) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
    fun i => |position i|

theorem abs_position_le_infiniteSelectionStateNorm {N : ℕ}
    (hN : 0 < N) (position : Fin N → ℝ) (i : Fin N) :
    |position i| ≤ infiniteSelectionStateNorm hN position := by
  exact Finset.le_sup' (fun j => |position j|) (Finset.mem_univ i)

/-- One generation changes the sup norm by at most the largest absolute
leftmost-child displacement, provided every parent has a leftmost child and
the slot enumeration is increasing. The first-`N` property is used in the
upper bound: the `N` slot-zero children are a competing set of `N` candidates. -/
theorem infiniteOffspringTransition_stateNorm_le {N : ℕ}
    (hN : 0 < N) (position : Fin N → ℝ)
    (offspring : Fin N → Step ℕ ℝ)
    (hgood : IsGoodInfiniteOffspringBatch offspring)
    (hordered : ∀ i, (offspring i).IsOrderedBy realPotential)
    (hfirst : ∀ i, survive (offspring i) 0) :
    infiniteSelectionStateNorm hN
        (infiniteOffspringTransition position offspring hgood) ≤
      infiniteSelectionStateNorm hN position +
        Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
          (fun i => |value' (offspring i) 0|) := by
  classical
  let B := infiniteSelectionStateNorm hN position
  let D := Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
    (fun i => |value' (offspring i) 0|)
  let value := infiniteOffspringPosition position offspring
  let selected := infiniteOffspringFirstN position offspring hgood.finiteWeight
  have hcard : selected.card = N := infiniteOffspringFirstN_card position offspring hgood
  have hspec := infiniteOffspringFirstN_spec position offspring hgood.finiteWeight
  have hnorm : ∀ i, |position i| ≤ B := by
    intro i
    exact abs_position_le_infiniteSelectionStateNorm hN position i
  have hdisp : ∀ i, |value' (offspring i) 0| ≤ D := by
    intro i
    exact Finset.le_sup' (fun j => |value' (offspring j) 0|) (Finset.mem_univ i)
  have horderedMap (i : Fin N) : (offspring i).map id ∈ orderedSteps := by
    simpa [Step.IsOrderedBy, realPotential] using hordered i
  have hzeroLe (i : Fin N) (j : ℕ) (hj : survive (offspring i) j) :
      value' (offspring i) 0 ≤ value' (offspring i) j := by
    have hmono := orderedSteps_value_mono ((offspring i).map id)
      (horderedMap i) (Nat.zero_le j) (by simpa using hj)
    simpa using hmono
  have hbaseCandidate (i : Fin N) :
      toLex (i, 0) ∈ infiniteOffspringCandidates offspring := by
    change survive (offspring (ofLex (toLex (i, 0))).1) (ofLex (toLex (i, 0))).2
    simpa using hfirst i
  have hbaseValue (i : Fin N) : value (toLex (i, 0)) ≤ B + D := by
    dsimp [value, infiniteOffspringPosition]
    have hiPos : position i ≤ B := (le_abs_self _).trans (hnorm i)
    have hiDisp : value' (offspring i) 0 ≤ D := (le_abs_self _).trans (hdisp i)
    linarith
  have hlabelInjective : Function.Injective (fun i : Fin N => toLex (i, 0)) := by
    intro i j hij
    have hfst := congrArg (fun q : InfiniteSlotLabel N => (ofLex q).1) hij
    simpa using hfst
  let base : Finset (InfiniteSlotLabel N) := Finset.univ.image (fun i : Fin N => toLex (i, 0))
  have hbaseCard : base.card = N := by
    change (Finset.univ.image (fun i : Fin N => toLex (i, 0))).card = N
    rw [Finset.card_image_of_injective _ hlabelInjective]
    simp
  have hbaseSubset : (↑base : Set (InfiniteSlotLabel N)) ⊆ infiniteOffspringCandidates offspring := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact hbaseCandidate i
  have hselectedUpper (q : InfiniteSlotLabel N) (hq : q ∈ selected) :
      value q ≤ B + D := by
    by_contra hnot
    have hstrict : B + D < value q := lt_of_not_ge hnot
    have hqNotBase : q ∉ base := by
      intro hqbase
      obtain ⟨i, -, hEq⟩ := Finset.mem_image.mp hqbase
      subst q
      exact (not_lt_of_ge (hbaseValue i)) hstrict
    have hbaseSelected : base ⊆ selected := by
      intro p hp
      obtain ⟨i, -, hEq⟩ := Finset.mem_image.mp hp
      rw [← hEq]
      apply hspec.lower q hq (toLex (i, 0)) (hbaseCandidate i)
      exact valueKey_lt_of_value_lt value (lt_of_le_of_lt (hbaseValue i) hstrict)
    have hcardLe : (base ∪ {q}).card ≤ selected.card := Finset.card_le_card (by
      intro p hp
      rcases Finset.mem_union.mp hp with hpBase | hpq
      · exact hbaseSelected hpBase
      · exact Finset.mem_singleton.mp hpq ▸ hq)
    have hdisjoint : Disjoint base {q} := Finset.disjoint_singleton_right.mpr hqNotBase
    rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_singleton,
      hbaseCard, hcard] at hcardLe
    omega
  have hselectedLower (q : InfiniteSlotLabel N) (hq : q ∈ selected) :
      -(B + D) ≤ value q := by
    have hqcand : q ∈ infiniteOffspringCandidates offspring := hspec.subset hq
    change survive (offspring (ofLex q).1) (ofLex q).2 at hqcand
    have hslot := hzeroLe (ofLex q).1 (ofLex q).2 hqcand
    dsimp [value, infiniteOffspringPosition]
    have hipos : -B ≤ position (ofLex q).1 := by
      exact le_trans (neg_le_of_abs_le (hnorm (ofLex q).1)) (by simp)
    have hidisp : -D ≤ value' (offspring (ofLex q).1) 0 :=
      le_trans (neg_le_of_abs_le (hdisp (ofLex q).1)) (by simp)
    linarith
  have hcoord (i : Fin N) :
      |infiniteOffspringTransition position offspring hgood i| ≤ B + D := by
    unfold infiniteOffspringTransition
    let q := selectedLabelAtRank value selected hcard i
    have hq : q ∈ selected := selectedLabelAtRank_mem value selected hcard i
    change |value q| ≤ B + D
    rw [abs_le]
    exact ⟨hselectedLower q hq, hselectedUpper q hq⟩
  unfold infiniteSelectionStateNorm
  apply Finset.sup'_le _ _
  intro i hi
  exact hcoord i

theorem infiniteOffspringTransition_mono
    {N : ℕ} (positionLow positionHigh : Fin N → ℝ)
    (offspring : Fin N → Step ℕ ℝ) (hgood : IsGoodInfiniteOffspringBatch offspring)
    (hposition : ∀ i, positionLow i ≤ positionHigh i) :
    ∀ i, infiniteOffspringTransition positionLow offspring hgood i ≤
      infiniteOffspringTransition positionHigh offspring hgood i := by
  exact infiniteOffspringPosition_select_mono positionLow positionHigh offspring
    (infiniteOffspringFirstN positionLow offspring hgood.finiteWeight)
    (infiniteOffspringFirstN positionHigh offspring hgood.finiteWeight)
    (infiniteOffspringFirstN_spec positionLow offspring hgood.finiteWeight)
    (infiniteOffspringFirstN_spec positionHigh offspring hgood.finiteWeight)
    (infiniteOffspringFirstN_card positionLow offspring hgood)
    (infiniteOffspringFirstN_card positionHigh offspring hgood)
    hposition

theorem infiniteOffspringFirstN_rank_monotone
    {N : ℕ} (position : Fin N → ℝ) (offspring : Fin N → Step ℕ ℝ)
    (hgood : IsGoodInfiniteOffspringBatch offspring) :
    Monotone (infiniteOffspringTransition position offspring hgood) := by
  intro i j hij
  let value := infiniteOffspringPosition position offspring
  let selected := infiniteOffspringFirstN position offspring hgood.finiteWeight
  let hcard := infiniteOffspringFirstN_card position offspring hgood
  have hiMem : selectedLabelAtRank value selected hcard i ∈ selected :=
    selectedLabelAtRank_mem value selected hcard i
  have hjMem : selectedLabelAtRank value selected hcard j ∈ selected :=
    selectedLabelAtRank_mem value selected hcard j
  by_contra hnot
  have hvalue : value (selectedLabelAtRank value selected hcard j) <
      value (selectedLabelAtRank value selected hcard i) := lt_of_not_ge hnot
  have hkey : valueKey value (selectedLabelAtRank value selected hcard j) <
      valueKey value (selectedLabelAtRank value selected hcard i) :=
    valueKey_lt_of_value_lt value hvalue
  let keys := selected.image (valueKey value)
  have hjKey : valueKey value (selectedLabelAtRank value selected hcard j) ∈ keys :=
    Finset.mem_image.mpr ⟨_, hjMem, rfl⟩
  have hrank := rank_lt_rank_of_lt hjKey hkey
  have hji := selectedLabelAtRank_rank value selected hcard j
  have hii := selectedLabelAtRank_rank value selected hcard i
  change rankBy value selected (selectedLabelAtRank value selected hcard j) <
    rankBy value selected (selectedLabelAtRank value selected hcard i) at hrank
  rw [hji, hii] at hrank
  exact (not_lt_of_ge (by exact_mod_cast hij)) hrank

/-- The ordered key map implementing common spatial translation. -/
def infinitePositionKeyShift {N : ℕ} (c : ℝ) :
    (ℝ ×ₗ InfiniteSlotLabel N) ≃o (ℝ ×ₗ InfiniteSlotLabel N) :=
  Prod.Lex.prodLexCongr (OrderIso.addRight c) (OrderIso.refl _)

theorem infiniteOffspringPositionKey_shift
    {N : ℕ} (value : InfiniteSlotLabel N → ℝ) (c : ℝ)
    (q : InfiniteSlotLabel N) :
    valueKey (fun p => value p + c) q =
      infinitePositionKeyShift c (valueKey value q) := by
  simp [infinitePositionKeyShift, valueKey]

theorem valueKey_add_const_lt_iff
    {N : ℕ} (value : InfiniteSlotLabel N → ℝ) (c : ℝ)
    (p q : InfiniteSlotLabel N) :
    valueKey (fun r => value r + c) p < valueKey (fun r => value r + c) q ↔
      valueKey value p < valueKey value q := by
  rw [infiniteOffspringPositionKey_shift, infiniteOffspringPositionKey_shift]
  exact (infinitePositionKeyShift c).lt_iff_lt

theorem rankBy_add_const
    {N : ℕ} (value : InfiniteSlotLabel N → ℝ) (selected : Finset (InfiniteSlotLabel N))
    (c : ℝ) (q : InfiniteSlotLabel N) :
    rankBy (fun p => value p + c) selected q = rankBy value selected q := by
  rw [rankBy_eq_card_filter, rankBy_eq_card_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp, hlt⟩
    refine ⟨hp, ?_⟩
    exact (valueKey_add_const_lt_iff value c p q).mp hlt
  · rintro ⟨hp, hlt⟩
    refine ⟨hp, ?_⟩
    exact (valueKey_add_const_lt_iff value c p q).mpr hlt

theorem isFirstNBy_add_const
    {N : ℕ} (value : InfiniteSlotLabel N → ℝ)
    (candidates : Set (InfiniteSlotLabel N)) (selected : Finset (InfiniteSlotLabel N))
    (hselected : IsFirstNBy N value candidates selected) (c : ℝ) :
    IsFirstNBy N (fun q => value q + c) candidates selected := by
  refine ⟨hselected.subset, hselected.card_finite, hselected.card_infinite, ?_⟩
  intro p hp q hq hqp
  apply hselected.lower p hp q hq
  exact (valueKey_add_const_lt_iff value c q p).mp hqp

theorem infiniteOffspringTransition_shift
    {N : ℕ} (position : Fin N → ℝ)
    (offspring : Fin N → Step ℕ ℝ) (hgood : IsGoodInfiniteOffspringBatch offspring)
    (c : ℝ) :
    infiniteOffspringTransition (fun i => position i + c) offspring hgood =
      fun i => infiniteOffspringTransition position offspring hgood i + c := by
  classical
  let value := infiniteOffspringPosition position offspring
  let selected := infiniteOffspringFirstN position offspring hgood.finiteWeight
  let shiftedValue := infiniteOffspringPosition (fun i => position i + c) offspring
  let shiftedSelected := infiniteOffspringFirstN (fun i => position i + c) offspring
    hgood.finiteWeight
  have hvalueEq : shiftedValue = fun q => value q + c := by
    funext q
    simp [shiftedValue, value, infiniteOffspringPosition]
    ring
  have hselectedShift : IsFirstNBy N shiftedValue
      (infiniteOffspringCandidates offspring) selected := by
    rw [hvalueEq]
    exact isFirstNBy_add_const value (infiniteOffspringCandidates offspring) selected
      (infiniteOffspringFirstN_spec position offspring hgood.finiteWeight) c
  have hselectedNew := infiniteOffspringFirstN_spec
    (fun i => position i + c) offspring hgood.finiteWeight
  have hselectedEq : shiftedSelected = selected :=
    hselectedNew.unique hselectedShift
  have hcard := infiniteOffspringFirstN_card position offspring hgood
  have hshiftCard := infiniteOffspringFirstN_card (fun i => position i + c)
    offspring hgood
  have hselectedShiftRank : ∀ i : Fin N,
      rankBy shiftedValue shiftedSelected
        (selectedLabelAtRank value selected hcard i) = i.val := by
    intro i
    calc
      rankBy shiftedValue shiftedSelected
          (selectedLabelAtRank value selected hcard i) =
          rankBy shiftedValue selected
            (selectedLabelAtRank value selected hcard i) := by rw [hselectedEq]
      _ = rankBy value selected (selectedLabelAtRank value selected hcard i) := by
        rw [hvalueEq, rankBy_add_const]
      _ = i.val := selectedLabelAtRank_rank value selected hcard i
  have hlabelEq : ∀ i : Fin N,
      selectedLabelAtRank shiftedValue shiftedSelected hshiftCard i =
        selectedLabelAtRank value selected hcard i := by
    intro i
    apply rankBy_injOn shiftedValue shiftedSelected
    · exact selectedLabelAtRank_mem shiftedValue shiftedSelected hshiftCard i
    · exact hselectedEq.symm ▸ selectedLabelAtRank_mem value selected hcard i
    · rw [selectedLabelAtRank_rank shiftedValue shiftedSelected hshiftCard i,
        hselectedShiftRank i]
  funext i
  change shiftedValue
      (selectedLabelAtRank shiftedValue shiftedSelected hshiftCard i) =
    value (selectedLabelAtRank value selected hcard i) + c
  rw [hlabelEq i, hvalueEq]


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end

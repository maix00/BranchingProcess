/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Basic
public import Combinatorics.BranchingWalk.Step.ExponentialWeight
public import Combinatorics.BranchingWalk.Step.Potential
public import Combinatorics.BranchingWalk.Step.Monotone
public import Combinatorics.BranchingWalk.Selection.NSelection.Hall
public import Combinatorics.BranchingWalk.Selection.NSelection.Matching
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Prod.Lex

/-!
# Variable-offspring selection for the speed argument

This file records a deterministic transition fact for the actual
optional-slot model.  A batch assigns an arbitrary `Step ℕ ℝ` to each of the
`N` current ranks; absent slots are excluded from the candidate set, and the
offspring slot type is countably infinite.  In particular, this is not the
fixed-slot/finite-capacity special case.

The theorem below proves that common offspring marks preserve coordinatewise
order after leftmost-`N` selection and rank reset.  Its hypotheses expose the
two genuine model obligations at a transition: both candidate sets admit a
first-`N` segment, and that segment has exactly `N` members.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open scoped ENNReal

/-- A parent-rank/child-slot label. The child-slot coordinate is `ℕ`, so
each parent can carry a finite, countable, or empty offspring set. -/
abbrev InfiniteSlotLabel (N : ℕ) := Fin N ×ₗ ℕ

/-- The present children in a batch of optional-slot offspring steps. -/
def infiniteOffspringCandidates {N : ℕ}
    (offspring : Fin N → Step ℕ ℝ) : Set (InfiniteSlotLabel N) :=
  {q | survive (offspring (ofLex q).1) (ofLex q).2}

/-- The absolute position of a child candidate from a ranked population. -/
def infiniteOffspringPosition {N : ℕ}
    (position : Fin N → ℝ) (offspring : Fin N → Step ℕ ℝ)
    (q : InfiniteSlotLabel N) : ℝ :=
  position (ofLex q).1 + value' (offspring (ofLex q).1) (ofLex q).2

/-- Recover the label at a given spatial rank in a finite selected set. -/
noncomputable def selectedLabelAtRank {N : ℕ}
    (value : InfiniteSlotLabel N → ℝ) (selected : Finset (InfiniteSlotLabel N))
    (hcard : selected.card = N) (i : Fin N) : InfiniteSlotLabel N :=
  Option.get (particleAtRankBy value selected i.val)
    (Option.isSome_iff_ne_none.mpr (by
      intro hnone
      rw [particleAtRankBy_eq_none_iff] at hnone
      rw [hcard] at hnone
      exact (not_le_of_gt i.isLt) hnone))

theorem selectedLabelAtRank_mem {N : ℕ}
    (value : InfiniteSlotLabel N → ℝ) (selected : Finset (InfiniteSlotLabel N))
    (hcard : selected.card = N) (i : Fin N) :
    selectedLabelAtRank value selected hcard i ∈ selected := by
  have hget : particleAtRankBy value selected i.val =
      some (selectedLabelAtRank value selected hcard i) := by
    exact (Option.some_get _).symm
  exact (particleAtRankBy_eq_some_iff.mp hget).1

theorem selectedLabelAtRank_rank {N : ℕ}
    (value : InfiniteSlotLabel N → ℝ) (selected : Finset (InfiniteSlotLabel N))
    (hcard : selected.card = N) (i : Fin N) :
    rankBy value selected (selectedLabelAtRank value selected hcard i) = i.val := by
  have hget : particleAtRankBy value selected i.val =
      some (selectedLabelAtRank value selected hcard i) := by
    exact (Option.some_get _).symm
  exact (particleAtRankBy_eq_some_iff.mp hget).2

/-- With the same optional offspring slots, lowering every parent position
lowers every selected spatial rank.  The proof handles arbitrary/countable
offspring populations through `IsFirstNBy` and Hall matching. -/
theorem infiniteOffspringPosition_select_mono
    {N : ℕ}
    (positionLow positionHigh : Fin N → ℝ)
    (offspring : Fin N → Step ℕ ℝ)
    (selectedLow selectedHigh : Finset (InfiniteSlotLabel N))
    (hLow : IsFirstNBy N (infiniteOffspringPosition positionLow offspring)
      (infiniteOffspringCandidates offspring) selectedLow)
    (hHigh : IsFirstNBy N (infiniteOffspringPosition positionHigh offspring)
      (infiniteOffspringCandidates offspring) selectedHigh)
    (hLowCard : selectedLow.card = N)
    (hHighCard : selectedHigh.card = N)
    (hposition : ∀ i, positionLow i ≤ positionHigh i) :
    ∀ i : Fin N,
      infiniteOffspringPosition positionLow offspring
          (selectedLabelAtRank (infiniteOffspringPosition positionLow offspring)
            selectedLow hLowCard i) ≤
        infiniteOffspringPosition positionHigh offspring
          (selectedLabelAtRank (infiniteOffspringPosition positionHigh offspring)
            selectedHigh hHighCard i) := by
  classical
  let lowValue := infiniteOffspringPosition positionLow offspring
  let highValue := infiniteOffspringPosition positionHigh offspring
  have hmatching := exists_injective_le_of_embedding_of_isFirstNBy
    N highValue lowValue selectedHigh (infiniteOffspringCandidates offspring)
    selectedLow hLow (by rw [hHighCard])
    (fun q => q)
    (by intro q hq; exact hHigh.subset hq)
    (by intro q hq r hr hqr; exact hqr)
    (by
      intro q hq
      dsimp [lowValue, highValue, infiniteOffspringPosition]
      linarith [hposition (ofLex q).1])
  obtain ⟨matchParticle, hmatchMem, hmatchLe, hmatchInj⟩ := hmatching
  have hthreshold : ∀ a : ℝ,
      (selectedHigh.filter fun q => highValue q ≤ a).card ≤
        (selectedLow.filter fun q => lowValue q ≤ a).card := by
    intro a
    let source := selectedHigh.filter fun q => highValue q ≤ a
    let target := selectedLow.filter fun q => lowValue q ≤ a
    let f : {q // q ∈ source} → {q // q ∈ target} := fun q =>
      ⟨matchParticle q.1 (Finset.mem_filter.mp q.2 |>.1),
        Finset.mem_filter.mpr ⟨
          hmatchMem q.1 (Finset.mem_filter.mp q.2 |>.1),
          (hmatchLe q.1 (Finset.mem_filter.mp q.2 |>.1)).trans
            (Finset.mem_filter.mp q.2 |>.2)⟩⟩
    have hf : Function.Injective f := by
      intro q r hqr
      apply Subtype.ext
      apply hmatchInj q.1 (Finset.mem_filter.mp q.2 |>.1)
        r.1 (Finset.mem_filter.mp r.2 |>.1)
      exact congrArg Subtype.val hqr
    simpa [source, target] using Finset.card_le_card_of_injective hf
  intro i
  let q := selectedLabelAtRank highValue selectedHigh hHighCard i
  have hq : q ∈ selectedHigh := by
    exact selectedLabelAtRank_mem highValue selectedHigh hHighCard i
  let r := matchByRank highValue lowValue selectedHigh selectedLow
    (by rw [hHighCard, hLowCard]) q hq
  have hr : r ∈ selectedLow :=
    matchByRank_mem highValue lowValue selectedHigh selectedLow
      (by rw [hHighCard, hLowCard]) q hq
  have hrank : rankBy lowValue selectedLow r = i.val := by
    rw [rankBy_matchByRank]
    exact selectedLabelAtRank_rank highValue selectedHigh hHighCard i
  have hrank' := selectedLabelAtRank_rank lowValue selectedLow hLowCard i
  have hEq : r = selectedLabelAtRank lowValue selectedLow hLowCard i :=
    rankBy_injOn lowValue selectedLow hr
      (selectedLabelAtRank_mem lowValue selectedLow hLowCard i)
      (hrank.trans hrank'.symm)
  rw [← hEq]
  exact matchByRank_value_le highValue lowValue selectedHigh selectedLow
    (by rw [hHighCard, hLowCard]) hthreshold q hq

/-- A batch is admissible when each parent has finite negative exponential
weight and the batch contains at least N present candidates.  Individual
parents may have no offspring; only the whole N-particle transition must have
enough candidates to continue. -/
structure IsGoodInfiniteOffspringBatch {N : ℕ}
    (offspring : Fin N → Step ℕ ℝ) : Prop where
  finiteWeight : ∀ i, totalChildWeight (offspring i) ≠ ∞
  enoughCandidates : ∃ s : Finset (InfiniteSlotLabel N),
    (↑s : Set (InfiniteSlotLabel N)) ⊆ infiniteOffspringCandidates offspring ∧
      s.card = N

theorem infiniteOffspringCandidates_lowerFinite
    {N : ℕ} (position : Fin N → ℝ) (offspring : Fin N → Step ℕ ℝ)
    (hweight : ∀ i, totalChildWeight (offspring i) ≠ ∞) :
    IsLowerFiniteBy (infiniteOffspringPosition position offspring)
      (infiniteOffspringCandidates offspring) := by
  classical
  intro p hp
  let bound := infiniteOffspringPosition position offspring p
  let boundedSlots : Fin N → Finset ℕ := fun i =>
    (finite_realized_children_below (offspring i) (hweight i)
      (bound - position i)).toFinset
  let boundedLabels : Finset (InfiniteSlotLabel N) :=
    Finset.univ.biUnion fun i =>
      (boundedSlots i).image fun j => toLex (i, j)
  have hfinite : (↑boundedLabels : Set (InfiniteSlotLabel N)).Finite :=
    boundedLabels.finite_toSet
  apply hfinite.subset
  intro q hq
  obtain ⟨hqCandidates, hqKey⟩ := hq
  have hqValue : infiniteOffspringPosition position offspring q ≤ bound :=
    Prod.Lex.monotone_fst_ofLex hqKey
  change q ∈ Finset.univ.biUnion (fun i =>
    (boundedSlots i).image fun j => toLex (i, j))
  rw [Finset.mem_biUnion]
  refine ⟨(ofLex q).1, Finset.mem_univ _, ?_⟩
  rw [Finset.mem_image]
  refine ⟨(ofLex q).2, ?_, ?_⟩
  · change (ofLex q).2 ∈
      (finite_realized_children_below (offspring (ofLex q).1)
        (hweight (ofLex q).1) (bound - position (ofLex q).1)).toFinset
    apply (finite_realized_children_below (offspring (ofLex q).1)
      (hweight (ofLex q).1) (bound - position (ofLex q).1)).mem_toFinset.mpr
    refine ⟨hqCandidates, ?_⟩
    dsimp [infiniteOffspringPosition] at hqValue
    linarith
  · simp

theorem infiniteOffspringCandidates_hasFiniteSubset_card
    {N : ℕ} (offspring : Fin N → Step ℕ ℝ)
    (hhasChild : ∀ i, ∃ j, survive (offspring i) j) :
    ∃ s : Finset (InfiniteSlotLabel N),
      (↑s : Set (InfiniteSlotLabel N)) ⊆ infiniteOffspringCandidates offspring ∧
      s.card = N := by
  classical
  let child : Fin N → ℕ := fun i => Classical.choose (hhasChild i)
  have hchild : ∀ i, survive (offspring i) (child i) :=
    fun i => Classical.choose_spec (hhasChild i)
  let label : Fin N → InfiniteSlotLabel N := fun i => toLex (i, child i)
  have hinjective : Function.Injective label := by
    intro i j hij
    have hfst := congrArg (fun q : InfiniteSlotLabel N => (ofLex q).1) hij
    simpa [label] using hfst
  refine ⟨Finset.univ.image label, ?_, ?_⟩
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact (by simpa [infiniteOffspringCandidates, label]
      using hchild i)
  · rw [Finset.card_image_of_injective _ hinjective]
    simp

theorem selectedFirstNBy_card_of_hasEnoughCandidates
    {N : ℕ} (value : InfiniteSlotLabel N → ℝ)
    (candidates : Set (InfiniteSlotLabel N)) (selected : Finset (InfiniteSlotLabel N))
    (hselected : IsFirstNBy N value candidates selected)
    (hhasChild : ∃ s : Finset (InfiniteSlotLabel N),
      (↑s : Set (InfiniteSlotLabel N)) ⊆ candidates ∧ s.card = N) :
    selected.card = N := by
  classical
  rcases candidates.finite_or_infinite with hfinite | hinfinite
  · obtain ⟨s, hs, hsCard⟩ := hhasChild
    have hN : N ≤ hfinite.toFinset.card := by
      calc
        N = s.card := hsCard.symm
        _ ≤ hfinite.toFinset.card := by
          apply Finset.card_le_card
          intro q hq
          exact hfinite.mem_toFinset.mpr (hs hq)
    rw [hselected.card_finite hfinite, min_eq_left hN]
  · exact hselected.card_infinite hinfinite

noncomputable def infiniteOffspringFirstN
    {N : ℕ} (position : Fin N → ℝ) (offspring : Fin N → Step ℕ ℝ)
    (hweight : ∀ i, totalChildWeight (offspring i) ≠ ∞) :
    Finset (InfiniteSlotLabel N) :=
  selectFirstNFromSet N (infiniteOffspringPosition position offspring)
    (infiniteOffspringCandidates offspring)
    (admitsFirstNBy_of_lowerFinite N _
      (infiniteOffspringCandidates_lowerFinite position offspring hweight))

theorem infiniteOffspringFirstN_spec
    {N : ℕ} (position : Fin N → ℝ) (offspring : Fin N → Step ℕ ℝ)
    (hweight : ∀ i, totalChildWeight (offspring i) ≠ ∞) :
    IsFirstNBy N (infiniteOffspringPosition position offspring)
      (infiniteOffspringCandidates offspring)
      (infiniteOffspringFirstN position offspring hweight) :=
  selectFirstNFromSet_spec N _ _ _

theorem infiniteOffspringFirstN_card
    {N : ℕ} (position : Fin N → ℝ) (offspring : Fin N → Step ℕ ℝ)
    (hgood : IsGoodInfiniteOffspringBatch offspring) :
    (infiniteOffspringFirstN position offspring hgood.finiteWeight).card = N := by
  apply selectedFirstNBy_card_of_hasEnoughCandidates
    (infiniteOffspringPosition position offspring)
    (infiniteOffspringCandidates offspring)
    (infiniteOffspringFirstN position offspring hgood.finiteWeight)
    (infiniteOffspringFirstN_spec position offspring hgood.finiteWeight)
  exact hgood.enoughCandidates

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

/-- Iterate the actual countable-offspring ranked transition in a fixed
environment indexed by generation and current rank. -/
noncomputable def infiniteOffspringRun
    {N : ℕ} (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (initial : Fin N → ℝ) : ℕ → Fin N → ℝ
  | 0 => initial
  | n + 1 => infiniteOffspringTransition
      (infiniteOffspringRun offspring hgood initial n) (offspring n) (hgood n)

@[simp] theorem infiniteOffspringRun_zero
    {N : ℕ} (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (initial : Fin N → ℝ) :
    infiniteOffspringRun offspring hgood initial 0 = initial := rfl

@[simp] theorem infiniteOffspringRun_succ
    {N : ℕ} (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (initial : Fin N → ℝ) (n : ℕ) :
    infiniteOffspringRun offspring hgood initial (n + 1) =
      infiniteOffspringTransition (infiniteOffspringRun offspring hgood initial n)
        (offspring n) (hgood n) := rfl

/-- The maximal absolute slot-zero displacement in one generation. -/
noncomputable def infiniteOffspringBatchSlotZeroNorm {N : ℕ} (hN : 0 < N)
    (offspring : Fin N → Step ℕ ℝ) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
    (fun i => |value' (offspring i) 0|)

/-- A deterministic trajectory bound: the sup norm of the population after
`n` generations is at most its initial norm plus the sum of the one-generation
leftmost-child envelopes. -/
theorem infiniteOffspringRun_stateNorm_le {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (hordered : ∀ t i, (offspring t i).IsOrderedBy realPotential)
    (hfirst : ∀ t i, survive (offspring t i) 0)
    (initial : Fin N → ℝ) (n : ℕ) :
    infiniteSelectionStateNorm hN (infiniteOffspringRun offspring hgood initial n) ≤
      infiniteSelectionStateNorm hN initial +
        ∑ t ∈ Finset.range n, infiniteOffspringBatchSlotZeroNorm hN (offspring t) := by
  induction n with
  | zero => simp [infiniteOffspringRun, infiniteSelectionStateNorm]
  | succ n ih =>
      rw [infiniteOffspringRun_succ]
      calc
        infiniteSelectionStateNorm hN
            (infiniteOffspringTransition (infiniteOffspringRun offspring hgood initial n)
              (offspring n) (hgood n)) ≤
            infiniteSelectionStateNorm hN (infiniteOffspringRun offspring hgood initial n) +
              infiniteOffspringBatchSlotZeroNorm hN (offspring n) := by
                exact infiniteOffspringTransition_stateNorm_le hN _ _ (hgood n)
                  (hordered n) (hfirst n)
        _ ≤ infiniteSelectionStateNorm hN initial +
              (∑ t ∈ Finset.range n, infiniteOffspringBatchSlotZeroNorm hN (offspring t)) +
              infiniteOffspringBatchSlotZeroNorm hN (offspring n) := by
                linarith [ih]
        _ = infiniteSelectionStateNorm hN initial +
              ∑ t ∈ Finset.range (n + 1), infiniteOffspringBatchSlotZeroNorm hN (offspring t) := by
                simp [Finset.sum_range_succ, add_assoc]

theorem infiniteOffspringRun_mono_initial
    {N : ℕ} (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (initialLow initialHigh : Fin N → ℝ)
    (hinitial : ∀ i, initialLow i ≤ initialHigh i) :
    ∀ n i, infiniteOffspringRun offspring hgood initialLow n i ≤
      infiniteOffspringRun offspring hgood initialHigh n i := by
  intro n
  induction n with
  | zero => exact hinitial
  | succ n ih =>
      intro i
      rw [infiniteOffspringRun_succ, infiniteOffspringRun_succ]
      exact infiniteOffspringTransition_mono _ _ _ (hgood n) ih i

theorem infiniteOffspringRun_monotone
    {N : ℕ} (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (initial : Fin N → ℝ) (hinitial : Monotone initial) :
    ∀ n, Monotone (infiniteOffspringRun offspring hgood initial n) := by
  intro n
  induction n with
  | zero => simpa using hinitial
  | succ n _ =>
      rw [infiniteOffspringRun_succ]
      exact infiniteOffspringFirstN_rank_monotone
        (infiniteOffspringRun offspring hgood initial n) (offspring n) (hgood n)

theorem infiniteOffspringRun_shift
    {N : ℕ} (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (initial : Fin N → ℝ) (c : ℝ) :
    ∀ n, infiniteOffspringRun offspring hgood (fun i => initial i + c) n =
      fun i => infiniteOffspringRun offspring hgood initial n i + c := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [infiniteOffspringRun_succ, infiniteOffspringRun_succ, ih,
        infiniteOffspringTransition_shift]

theorem infiniteOffspringRun_split
    {N : ℕ} (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (initial : Fin N → ℝ) (m n : ℕ) :
    infiniteOffspringRun offspring hgood initial (m + n) =
      infiniteOffspringRun (fun t => offspring (m + t))
        (fun t => hgood (m + t))
        (infiniteOffspringRun offspring hgood initial m) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, infiniteOffspringRun_succ, ih, infiniteOffspringRun_succ]

theorem infiniteOffspringRun_congr
    {N : ℕ} (offspring offspring' : ℕ → Fin N → Step ℕ ℝ)
    (hmarks : offspring = offspring')
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (hgood' : ∀ t, IsGoodInfiniteOffspringBatch (offspring' t))
    (initial : Fin N → ℝ) (n : ℕ) :
    infiniteOffspringRun offspring hgood initial n =
      infiniteOffspringRun offspring' hgood' initial n := by
  cases hmarks
  have hgoodEq : hgood = hgood' := by
    funext t
    exact Subsingleton.elim _ _
  rw [hgoodEq]

/-- The leftmost position after a block of the fixed optional-offspring
environment, started from N particles at the common origin. -/
noncomputable def infiniteSelectionBlockMinimum
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (start length : ℕ) : ℝ :=
  infiniteOffspringRun (fun t => offspring (start + t))
    (fun t => hgood (start + t)) (fun _ => 0) length ⟨0, hN⟩

theorem infiniteSelectionBlockMinimum_subadditive
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (start firstLength secondLength : ℕ) :
    infiniteSelectionBlockMinimum hN offspring hgood start
        (firstLength + secondLength) ≥
      infiniteSelectionBlockMinimum hN offspring hgood start firstLength +
        infiniteSelectionBlockMinimum hN offspring hgood (start + firstLength)
          secondLength := by
  let origin : Fin N := ⟨0, hN⟩
  have horigin : ∀ i : Fin N, origin ≤ i := by
    intro i
    apply Fin.le_iff_val_le_val.mpr
    exact Nat.zero_le i.val
  let firstMarks := fun t => offspring (start + t)
  let firstGood := fun t => hgood (start + t)
  let state := infiniteOffspringRun firstMarks firstGood (fun _ => 0) firstLength
  have hstateMonotone : Monotone state := by
    exact infiniteOffspringRun_monotone firstMarks firstGood (fun _ => 0)
      (by intro i j hij; exact le_rfl) firstLength
  have hstateMin : ∀ i, state origin ≤ state i := by
    intro i
    exact hstateMonotone (horigin i)
  let commonStart : Fin N → ℝ := fun _ => state origin
  let laterMarks := fun t => offspring (start + firstLength + t)
  let laterGood := fun t => hgood (start + firstLength + t)
  let splitMarks := fun t => firstMarks (firstLength + t)
  let splitGood := fun t => firstGood (firstLength + t)
  have hcompare := infiniteOffspringRun_mono_initial laterMarks laterGood
    commonStart state hstateMin secondLength origin
  have hshift := infiniteOffspringRun_shift laterMarks laterGood (fun _ => 0)
    (state origin) secondLength
  have htranslated :
      infiniteOffspringRun laterMarks laterGood commonStart secondLength origin =
        infiniteOffspringRun laterMarks laterGood (fun _ => 0) secondLength origin +
          state origin := by
    have h := congrArg (fun f : Fin N → ℝ => f origin) hshift
    simpa [commonStart] using h
  have hsplit := infiniteOffspringRun_split firstMarks firstGood
    (fun _ => 0) firstLength secondLength
  have hsplit' :
      infiniteOffspringRun firstMarks firstGood (fun _ => 0)
        (firstLength + secondLength) =
      infiniteOffspringRun laterMarks laterGood state secondLength := by
    calc
      infiniteOffspringRun firstMarks firstGood (fun _ => 0)
          (firstLength + secondLength) =
        infiniteOffspringRun splitMarks splitGood state secondLength := by
          simpa [splitMarks, firstMarks, firstGood, state] using hsplit
      _ = infiniteOffspringRun laterMarks laterGood state secondLength :=
        infiniteOffspringRun_congr splitMarks laterMarks
          (by
            funext t
            dsimp [splitMarks, firstMarks, laterMarks]
            exact congrArg offspring (Nat.add_assoc start firstLength t).symm)
          splitGood laterGood state secondLength
  change infiniteOffspringRun firstMarks firstGood (fun _ => 0)
      (firstLength + secondLength) origin ≥
    infiniteOffspringRun firstMarks firstGood (fun _ => 0) firstLength origin +
      infiniteOffspringRun (fun t => offspring (start + firstLength + t))
        (fun t => hgood (start + firstLength + t)) (fun _ => 0)
        secondLength origin
  rw [hsplit']
  rw [add_comm (state origin)
    (infiniteOffspringRun laterMarks laterGood (fun _ => 0) secondLength origin)]
  rw [← htranslated]
  exact hcompare

/-- Negative block minima form a subadditive array indexed by a start time
and a block length. -/
noncomputable def infiniteSelectionSubadditiveArray
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (start length : ℕ) : ℝ :=
  - infiniteSelectionBlockMinimum hN offspring hgood start length

/-- Under an increasing slot enumeration with one leftmost child for every
parent, the absolute displacement of the left endpoint is controlled by the
sum of the generation-wise leftmost-child envelopes. -/
theorem infiniteSelectionSubadditiveArray_abs_le {N : ℕ}
    (hN : 0 < N) (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (hordered : ∀ t i, (offspring t i).IsOrderedBy realPotential)
    (hfirst : ∀ t i, survive (offspring t i) 0) (n : ℕ) :
    |infiniteSelectionSubadditiveArray hN offspring hgood 0 n| ≤
      ∑ t ∈ Finset.range n, infiniteOffspringBatchSlotZeroNorm hN (offspring t) := by
  unfold infiniteSelectionSubadditiveArray infiniteSelectionBlockMinimum
  have hrun := infiniteOffspringRun_stateNorm_le hN offspring hgood
    hordered hfirst (fun _ => 0) n
  have hcoord : |infiniteOffspringRun offspring hgood (fun _ => 0) n ⟨0, hN⟩| ≤
      infiniteSelectionStateNorm hN
        (infiniteOffspringRun offspring hgood (fun _ => 0) n) :=
    abs_position_le_infiniteSelectionStateNorm hN _ ⟨0, hN⟩
  have hinitialNorm : infiniteSelectionStateNorm hN (fun _ : Fin N => (0 : ℝ)) = 0 := by
    unfold infiniteSelectionStateNorm
    rw [Finset.sup'_const]
    simp
  rw [hinitialNorm] at hrun
  simpa [infiniteSelectionStateNorm] using hcoord.trans hrun

theorem infiniteSelectionSubadditiveArray_subadditive
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (start firstLength secondLength : ℕ) :
    infiniteSelectionSubadditiveArray hN offspring hgood start
        (firstLength + secondLength) ≤
      infiniteSelectionSubadditiveArray hN offspring hgood start firstLength +
        infiniteSelectionSubadditiveArray hN offspring hgood (start + firstLength)
          secondLength := by
  unfold infiniteSelectionSubadditiveArray
  linarith [infiniteSelectionBlockMinimum_subadditive hN offspring hgood
    start firstLength secondLength]

/-- A deterministic shift of the generation environment shifts the starting
time of every block. This is the pathwise stationarity identity; a
measure-preserving law for the environment turns it into distributional
stationarity. -/
theorem infiniteSelectionBlockMinimum_shift_covariant
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (shift start length : ℕ) :
    infiniteSelectionBlockMinimum hN
        (fun t => offspring (shift + t)) (fun t => hgood (shift + t))
        start length =
      infiniteSelectionBlockMinimum hN offspring hgood (shift + start) length := by
  unfold infiniteSelectionBlockMinimum
  have hrun := infiniteOffspringRun_congr
    (fun t => offspring (shift + (start + t)))
    (fun t => offspring (shift + start + t))
    (by
      funext t
      exact congrArg offspring (Nat.add_assoc shift start t).symm)
    (fun t => hgood (shift + (start + t)))
    (fun t => hgood (shift + start + t))
    (fun _ => 0)
    length
  exact congrArg (fun f : Fin N → ℝ => f ⟨0, hN⟩) hrun

theorem infiniteSelectionSubadditiveArray_shift_covariant
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (shift start length : ℕ) :
    infiniteSelectionSubadditiveArray hN
        (fun t => offspring (shift + t)) (fun t => hgood (shift + t))
        start length =
      infiniteSelectionSubadditiveArray hN offspring hgood (shift + start) length := by
  simp only [infiniteSelectionSubadditiveArray,
    infiniteSelectionBlockMinimum_shift_covariant]

/-- Endpoint-indexed version of the block array, defined for all pairs by
using truncated subtraction. The subadditive statements below use ordered
endpoints. -/
noncomputable def infiniteSelectionEndpointArray
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (start endpoint : ℕ) : ℝ :=
  infiniteSelectionSubadditiveArray hN offspring hgood start (endpoint - start)

theorem infiniteSelectionEndpointArray_subadditive
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (start firstLength secondLength : ℕ) :
    infiniteSelectionEndpointArray hN offspring hgood 0 (start + firstLength + secondLength) ≤
      infiniteSelectionEndpointArray hN offspring hgood 0 start +
        infiniteSelectionEndpointArray hN offspring hgood start
          (start + firstLength + secondLength) := by
  simpa [infiniteSelectionEndpointArray, Nat.add_assoc,
    Nat.add_sub_cancel_left] using
    infiniteSelectionSubadditiveArray_subadditive hN offspring hgood
      0 start (firstLength + secondLength)

theorem infiniteSelectionEndpointArray_shift_covariant
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (shift start endpoint : ℕ) (horder : start ≤ endpoint) :
    infiniteSelectionEndpointArray hN
        (fun t => offspring (shift + t)) (fun t => hgood (shift + t))
        start endpoint =
      infiniteSelectionEndpointArray hN offspring hgood
        (shift + start) (shift + endpoint) := by
  have hlength : (shift + endpoint) - (shift + start) = endpoint - start := by
    omega
  simp only [infiniteSelectionEndpointArray]
  rw [hlength, infiniteSelectionSubadditiveArray_shift_covariant]


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end

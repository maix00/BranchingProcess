/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Combinatorics.BranchingWalk.Step.Basic
public import Combinatorics.BranchingWalk.Step.Measure.ExponentialWeight
public import Combinatorics.BranchingWalk.Step.Potential
public import Combinatorics.BranchingWalk.Step.Ordering.ByPotential
public import Combinatorics.BranchingWalk.Step.Ordering.Monotone
public import Combinatorics.Selection.NSelection.Matching.Hall
public import Combinatorics.Selection.NSelection.Matching.ByRank
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Prod.Lex

/-!
# Optional-slot offspring batches

## Public declarations

For a batch of N parents with possibly empty, finite, or countably infinite
offspring, these declarations encode present child slots, their positions, and
leftmost-N selection. IsGoodInfiniteOffspringBatch requires finite total
exponential weight for each parent and at least N present candidates.

The declarations in
ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed are:
InfiniteSlotLabel (a parent rank and natural-number child slot),
infiniteOffspringCandidates, infiniteOffspringPosition, and
selectedLabelAtRank. The selection facts selectedLabelAtRank_mem and
selectedLabelAtRank_rank identify the selected label and its rank.
infiniteOffspringPosition_select_mono states that coordinatewise lowering
parent positions lowers every rank after common-mark leftmost-N selection.

infiniteOffspringCandidates_lowerFinite proves lower finiteness from finite
parent weights. infiniteOffspringCandidates_hasFiniteSubset_card constructs N
present candidates when each parent has a child.
selectedFirstNBy_card_of_hasEnoughCandidates proves the selected set has
cardinality N when N candidates exist. infiniteOffspringFirstN,
infiniteOffspringFirstN_spec, and infiniteOffspringFirstN_card construct the
selected batch, certify its IsFirstNBy property, and give its cardinality.

Write \(V_x(q)=\texttt{infiniteOffspringPosition}(x,b,q)\), and let
\(q_i^x\) be the label selected at rank i from state x. The order theorem
states
\[
  (\forall i<N,\; x_i\le y_i)
  \;\Longrightarrow\;
  (\forall i<N,\; V_x(q_i^x)\le V_y(q_i^y)).
\]
A good batch b has
\[
  \forall i,\; \mathrm{totalChildWeight}(b_i) < \infty,
  \qquad |\{q : q \text{ is present in } b\}| \ge N.
\]

This model follows the countably infinite offspring setting for the
N-branching random walk with selection in Cortines and Mallein,
“A N-branching random walk with random selection,” *ALEA* 14 (2017),
117–137, Section 1. Their \(\beta=\infty\) convention selects the N
rightmost particles; this file uses the order-dual convention and selects the
leftmost N. Optional natural-number slots give the formal model a countable
label space while allowing each parent to have a finite or infinite set of
present children.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open scoped ENNReal

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


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end

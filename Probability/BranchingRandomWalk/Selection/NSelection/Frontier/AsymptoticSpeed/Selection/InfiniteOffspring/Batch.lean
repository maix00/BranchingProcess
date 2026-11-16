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
public import Combinatorics.Selection.NSelection.Matching.SelectedPopulation
public import Combinatorics.Selection.NSelection.Matching.ByRank
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Optional-slot offspring batches

## Public declarations

For a batch of N parents with possibly empty, finite, or countably infinite
offspring, these declarations encode present child slots, their positions, and
leftmost-N selection. IsGoodInfiniteOffspringBatch requires finite total
exponential weight for each parent and at least N present candidates.

The declarations in
ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed are:
InfiniteSlotLabel (a parent rank and natural-number child slot),
infiniteOffspringCandidates, infiniteOffspringPosition, and
selectedLabelAtRank. The selection facts selectedLabelAtRank_mem and
selectedLabelAtRank_rank identify the selected label and its rank.
infiniteOffspringPosition_select_mono_of_capacity_le gives
$T_{N_2}(x^2)_i \le T_{N_1}(x^1)_i$ for $N_1 \le N_2$ and $i<N_1$
when $x_i^2 \le x_i^1$ and the offspring marks agree on common ranks.
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

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

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

/-- At common parent ranks use the same optional offspring slots. If the
larger population starts to the left at these ranks, each of its corresponding
selected ranks is also to the left. -/
theorem infiniteOffspringPosition_select_mono_of_capacity_le
    {N₁ N₂ : ℕ} (hcapacity : N₁ ≤ N₂)
    (positionSmall : Fin N₁ → ℝ) (positionLarge : Fin N₂ → ℝ)
    (offspring : Fin N₂ → Step ℕ ℝ)
    (selectedSmall : Finset (InfiniteSlotLabel N₁))
    (selectedLarge : Finset (InfiniteSlotLabel N₂))
    (hSmall : IsFirstNBy N₁
      (infiniteOffspringPosition positionSmall (offspring ∘ Fin.castLE hcapacity))
      (infiniteOffspringCandidates (offspring ∘ Fin.castLE hcapacity)) selectedSmall)
    (hLarge : IsFirstNBy N₂ (infiniteOffspringPosition positionLarge offspring)
      (infiniteOffspringCandidates offspring) selectedLarge)
    (hSmallCard : selectedSmall.card = N₁) (hLargeCard : selectedLarge.card = N₂)
    (hposition : ∀ i, positionLarge (Fin.castLE hcapacity i) ≤ positionSmall i) :
    ∀ i : Fin N₁,
      infiniteOffspringPosition positionLarge offspring
          (selectedLabelAtRank (infiniteOffspringPosition positionLarge offspring)
            selectedLarge hLargeCard (Fin.castLE hcapacity i)) ≤
        infiniteOffspringPosition positionSmall (offspring ∘ Fin.castLE hcapacity)
          (selectedLabelAtRank
            (infiniteOffspringPosition positionSmall (offspring ∘ Fin.castLE hcapacity))
            selectedSmall hSmallCard i) := by
  classical
  let smallValue := infiniteOffspringPosition positionSmall (offspring ∘ Fin.castLE hcapacity)
  let largeValue := infiniteOffspringPosition positionLarge offspring
  let sameSlot (q : InfiniteSlotLabel N₁) : InfiniteSlotLabel N₂ :=
    toLex (Fin.castLE hcapacity (ofLex q).1, (ofLex q).2)
  have hmatching := exists_injective_le_of_partnerAssignment_into_firstNBy
    N₂ smallValue largeValue selectedSmall (infiniteOffspringCandidates offspring)
    selectedLarge hLarge (hSmallCard.trans_le hcapacity)
    (fun q : {q // q ∈ selectedSmall} => sameSlot q.1)
    (by intro q; exact hSmall.subset q.2)
    (by
      intro q r hqr
      apply Subtype.ext
      have hparent := congrArg (fun z : InfiniteSlotLabel N₂ => (ofLex z).1) hqr
      have hslot := congrArg (fun z : InfiniteSlotLabel N₂ => (ofLex z).2) hqr
      have hpair : ofLex q.1 = ofLex r.1 :=
        Prod.ext (Fin.castLE_injective hcapacity hparent) hslot
      exact congrArg toLex hpair)
    (by
      intro q
      exact add_le_add (hposition (ofLex q.1).1) le_rfl)
  obtain ⟨partnerOfObject, hmatchMem, hmatchLe, hmatchInj⟩ := hmatching
  have hthreshold : ∀ a : ℝ,
      (selectedSmall.filter fun q => smallValue q ≤ a).card ≤
        (selectedLarge.filter fun q => largeValue q ≤ a).card := by
    intro a
    let selectedSmallAtMostA := selectedSmall.filter fun q => smallValue q ≤ a
    let selectedLargeAtMostA := selectedLarge.filter fun q => largeValue q ≤ a
    let f : {q // q ∈ selectedSmallAtMostA} → {q // q ∈ selectedLargeAtMostA} := fun q =>
      ⟨partnerOfObject q.1 (Finset.mem_filter.mp q.2 |>.1),
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
    simpa [selectedSmallAtMostA, selectedLargeAtMostA] using Finset.card_le_card_of_injective hf
  intro i
  exact partnerOrderKey_le_of_rankBy_eq_of_filter_card_le smallValue largeValue
    selectedSmall selectedLarge hthreshold
    (selectedLabelAtRank_mem smallValue selectedSmall hSmallCard i)
    ((selectedLabelAtRank_rank largeValue selectedLarge hLargeCard
      (Fin.castLE hcapacity i)).trans
        (selectedLabelAtRank_rank smallValue selectedSmall hSmallCard i).symm)

/-- At fixed capacity, lowering every starting position lowers each selected
rank under the same offspring marks. -/
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
  exact infiniteOffspringPosition_select_mono_of_capacity_le (le_refl N)
    positionHigh positionLow offspring selectedHigh selectedLow hHigh hLow
    hHighCard hLowCard hposition

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


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

end

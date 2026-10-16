/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.InitialPopulation.Speed.Basic
/-!
# The ranked-batch representation of a finite selected trajectory

This file compares a finite root-indexed N-selection process with the
ranked-batch recursion used by the speed theorem. Candidate children are
identified by their ranked parent and offspring slot; value thresholds make
the comparison independent of address tie breaks.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.UlamHarris
open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed

attribute [local instance] Classical.propDecidable Classical.decEq

private noncomputable def rankedPopulation
    (N n : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ) :
    Finset (RootIndexed.TreeNode (Fin N) ℕ) :=
  RootIndexed.selectedPopulationTotalized N Finset.univ initial id id n field

private noncomputable def rankedRoots
    (N n : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ) :
    Fin N → RootIndexed.TreeNode (Fin N) ℕ :=
  selectedPopulationRankRoots N initial n field

private lemma rankedRoots_image_eq_of_card
    (N n : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ)
    (hcard : (rankedPopulation N n initial field).card = N) :
    Finset.univ.image (rankedRoots N n initial field) =
      rankedPopulation N n initial field := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact (selectedPopulationRankRoot_mem_and_rank_of_card N n initial field i
      (by simpa [rankedPopulation] using hcard)).1
  · rw [Finset.card_image_of_injective _
      (by simpa [rankedRoots] using
        selectedPopulationRankRoots_injective N n initial field)]
    simpa [rankedPopulation] using hcard.le

private noncomputable def rankedChildAddress
    (N n : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ)
    (q : InfiniteSlotLabel N) : RootIndexed.TreeNode (Fin N) ℕ :=
  let slot := ofLex q
  let p := rankedRoots N n initial field slot.1
  (p.1, p.2 ++ [slot.2])

private lemma rankedRoot_batch_value
    (N n : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ)
    (i : Fin N) :
    selectedRootBatch (selectedPopulationRankRoots N initial) n field i =
      field (rankedRoots N n initial field i).1
        (rankedRoots N n initial field i).2 := by
  simp [selectedRootBatch, rootStepBatch,
    RootIndexed.selectedSubtreeStepFieldVector,
    RootIndexed.subtreeStepFieldVector, rankedRoots,
    selectedPopulationRankRoots]

private lemma rankedChildAddress_candidateImage
    (N n : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ)
    (hcard : (rankedPopulation N n initial field).card = N) :
    Set.image (rankedChildAddress N n initial field)
        (infiniteOffspringCandidates
          (selectedRootBatch (selectedPopulationRankRoots N initial) n field)) =
      RootIndexed.childrenAtGeneration n
        (rankedPopulation N n initial field) field := by
  classical
  let roots := rankedRoots N n initial field
  let population := rankedPopulation N n initial field
  let batch := selectedRootBatch (selectedPopulationRankRoots N initial) n field
  have hroots : Finset.univ.image roots = population :=
    rankedRoots_image_eq_of_card N n initial field hcard
  ext q
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hsurvive : survive (batch (ofLex r).1) (ofLex r).2 := by
      exact (show r ∈ infiniteOffspringCandidates batch from hr)
    have hparent : roots (ofLex r).1 ∈ population := by
      rw [← hroots]
      exact Finset.mem_image.mpr ⟨(ofLex r).1, Finset.mem_univ _, rfl⟩
    have hdepth : (roots (ofLex r).1).2.length = n := by
      exact selectedPopulationRankRoot_depth N n initial field (ofLex r).1
    have hsurvive' : survive (field (roots (ofLex r).1).1
        (roots (ofLex r).1).2) (ofLex r).2 := by
      simpa [batch, rankedRoot_batch_value, roots] using hsurvive
    exact RootIndexed.childAddress_mem_childrenAtGeneration n population field
      (roots (ofLex r).1) hparent hdepth (ofLex r).2 hsurvive'
  · intro hq
    obtain ⟨p, hp, hpdepth, j, hj, rfl⟩ :=
      (RootIndexed.mem_childrenAtGeneration_iff n population field q).mp hq
    rw [← hroots] at hp
    obtain ⟨i, _, hroot⟩ := Finset.mem_image.mp hp
    refine ⟨toLex (i, j), ?_, ?_⟩
    · change survive (batch (ofLex (toLex (i, j))).1)
        (ofLex (toLex (i, j))).2
      have hsurvive : survive (batch i) j := by
        simpa [batch, rankedRoot_batch_value, roots, hroot] using hj
      simpa using hsurvive
    · change ((roots i).1, (roots i).2 ++ [j]) = (p.1, p.2 ++ [j])
      exact congrArg (fun x : RootIndexed.TreeNode (Fin N) ℕ =>
        (x.1, x.2 ++ [j])) hroot

private lemma rankedChildAddress_injective
    (N n : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ) :
    Function.Injective (rankedChildAddress N n initial field) := by
  intro q r h
  let roots := rankedRoots N n initial field
  have hparent := congrArg Combinatorics.Branching.parent h
  have hroots : roots (ofLex q).1 = roots (ofLex r).1 := by
    simpa [rankedChildAddress, roots, Combinatorics.Branching.parent] using hparent
  have hindex : (ofLex q).1 = (ofLex r).1 := by
    exact selectedPopulationRankRoots_injective N n initial field hroots
  have hpath : (roots (ofLex q).1).2 ++ [(ofLex q).2] =
      (roots (ofLex r).1).2 ++ [(ofLex r).2] := by
    simpa [rankedChildAddress, roots] using congrArg Prod.snd h
  rw [hroots] at hpath
  have hslotList : [(ofLex q).2] = [(ofLex r).2] :=
    List.append_cancel_left hpath
  have hslot : (ofLex q).2 = (ofLex r).2 := by simpa using hslotList
  exact ofLex.injective (Prod.ext hindex hslot)

private lemma firstNBy_card_eq_of_hasEnoughCandidates
    {ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    {N : ℕ} (value : ι → Value) (candidates : Set ι)
    (selected : Finset ι)
    (hselected : IsFirstNBy N value candidates selected)
    (henough : ∃ s : Finset ι, (↑s : Set ι) ⊆ candidates ∧ s.card = N) :
    selected.card = N := by
  classical
  rcases candidates.finite_or_infinite with hfinite | hinfinite
  · obtain ⟨s, hs, hscard⟩ := henough
    have hN : N ≤ hfinite.toFinset.card := by
      calc
        N = s.card := hscard.symm
        _ ≤ hfinite.toFinset.card := Finset.card_le_card fun q hq =>
          hfinite.mem_toFinset.mpr (hs hq)
    rw [hselected.card_finite hfinite, min_eq_left hN]
  · exact hselected.card_infinite hinfinite

private lemma rankedPopulation_succ_card_of_good
    (N n : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ)
    (hcard : (rankedPopulation N n initial field).card = N)
    (hgood : IsGoodInfiniteOffspringBatch
      (selectedRootBatch (selectedPopulationRankRoots N initial) n field)) :
    (rankedPopulation N (n + 1) initial field).card = N := by
  classical
  let roots := rankedRoots N n initial field
  let population := rankedPopulation N n initial field
  let batch := selectedRootBatch (selectedPopulationRankRoots N initial) n field
  let value := RootIndexed.observedPositionAtGeneration initial id id (n + 1) field
  let candidates := RootIndexed.childrenAtGeneration n population field
  let selected := rankedPopulation N (n + 1) initial field
  have hroots : Finset.univ.image roots = population :=
    rankedRoots_image_eq_of_card N n initial field hcard
  have hweight : ∀ p ∈ population,
      totalPotentialWeight realPotential (-1) (field p.1 p.2) ≠ ∞ := by
    intro p hp
    rw [← hroots] at hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    have hi := hgood.finiteWeight i
    simpa [batch, rankedRoot_batch_value, roots,
      totalPotentialWeight_real_neg_one] using hi
  have hdepth : ∀ p ∈ population, p.2.length = n := by
    intro p hp
    exact RootIndexed.selectedPopulationTotalized_depth
      N Finset.univ initial id id n field p (by simpa [population, rankedPopulation] using hp)
  have hselector := RootIndexed.childrenAtGeneration_isLowerFiniteBy_real
    n population field initial hdepth hweight
  have hspec := RootIndexed.selectedPopulationTotalized_succ_spec
    N Finset.univ initial id id n field hselector
  have himage : Set.image (rankedChildAddress N n initial field)
      (infiniteOffspringCandidates batch) = candidates := by
    simpa [batch, candidates, population, rankedRoots, rankedPopulation] using
      rankedChildAddress_candidateImage N n initial field hcard
  have henough : ∃ s : Finset (RootIndexed.TreeNode (Fin N) ℕ),
      (↑s : Set (RootIndexed.TreeNode (Fin N) ℕ)) ⊆ candidates ∧ s.card = N := by
    obtain ⟨s, hs, hscard⟩ := hgood.enoughCandidates
    refine ⟨s.image (rankedChildAddress N n initial field), ?_, ?_⟩
    · intro q hq
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
      have hr' : r ∈ infiniteOffspringCandidates batch := hs hr
      have hmem : rankedChildAddress N n initial field r ∈
          Set.image (rankedChildAddress N n initial field)
            (infiniteOffspringCandidates batch) :=
        Set.mem_image_of_mem _ hr'
      rw [himage] at hmem
      exact hmem
    · rw [Finset.card_image_of_injective _
        (rankedChildAddress_injective N n initial field)]
      exact hscard
  have hselectedCard := firstNBy_card_eq_of_hasEnoughCandidates
    value candidates selected hspec henough
  simpa [selected, population, rankedPopulation] using hselectedCard

noncomputable def selectedPopulationRankPosition
    (N n : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ) : Fin N → ℝ :=
  fun i => RootIndexed.observedPositionAtGeneration initial id id n field
    (rankedRoots N n initial field i)

theorem rankedPopulation_card_eq_of_rankedBatches_good
    (N : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ)
    (hgood : ∀ n, IsGoodInfiniteOffspringBatch
      (selectedRootBatch (selectedPopulationRankRoots N initial) n field)) :
    ∀ n, (rankedPopulation N n initial field).card = N := by
  intro n
  induction n with
  | zero =>
      change (RootIndexed.initialPopulation (α := ℕ)
        (Finset.univ : Finset (Fin N))).card = N
      rw [RootIndexed.initialPopulation_card]
      simp
  | succ n ih =>
      exact rankedPopulation_succ_card_of_good N n initial field ih (hgood n)

/-- The same full-cardinality statement with the public root-indexed
population, for use by modules that do not have access to the private ranked
population abbreviation. -/
theorem selectedPopulationTotalized_card_eq_of_rankedBatches_good
    (N : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ)
    (hgood : ∀ n, IsGoodInfiniteOffspringBatch
      (selectedRootBatch (selectedPopulationRankRoots N initial) n field)) :
    ∀ n, (RootIndexed.selectedPopulationTotalized N Finset.univ
      initial id id n field).card = N := by
  simpa [rankedPopulation] using
    rankedPopulation_card_eq_of_rankedBatches_good N initial field hgood

private lemma rankedPosition_succ_eq_transition
    (N n : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ)
    (hcard : (rankedPopulation N n initial field).card = N)
    (hgood : IsGoodInfiniteOffspringBatch
      (selectedRootBatch (selectedPopulationRankRoots N initial) n field))
    (i : Fin N) :
    selectedPopulationRankPosition N (n + 1) initial field i =
      infiniteOffspringTransition (selectedPopulationRankPosition N n initial field)
        (selectedRootBatch (selectedPopulationRankRoots N initial) n field) hgood i := by
  classical
  let roots := rankedRoots N n initial field
  let population := rankedPopulation N n initial field
  let batch := selectedRootBatch (selectedPopulationRankRoots N initial) n field
  let valueLeft := RootIndexed.observedPositionAtGeneration initial id id (n + 1) field
  let candidatesLeft := RootIndexed.childrenAtGeneration n population field
  let selectedLeft := rankedPopulation N (n + 1) initial field
  let valueRight := infiniteOffspringPosition (selectedPopulationRankPosition N n initial field) batch
  let candidatesRight := infiniteOffspringCandidates batch
  let selectedRight := infiniteOffspringFirstN
    (selectedPopulationRankPosition N n initial field) batch hgood.finiteWeight
  have hroots : Finset.univ.image roots = population :=
    rankedRoots_image_eq_of_card N n initial field hcard
  have hweight : ∀ p ∈ population,
      totalPotentialWeight realPotential (-1) (field p.1 p.2) ≠ ∞ := by
    intro p hp
    rw [← hroots] at hp
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hp
    have hr := hgood.finiteWeight r
    simpa [batch, rankedRoot_batch_value, roots,
      totalPotentialWeight_real_neg_one] using hr
  have hdepth : ∀ p ∈ population, p.2.length = n := by
    intro p hp
    exact RootIndexed.selectedPopulationTotalized_depth
      N Finset.univ initial id id n field p (by simpa [population, rankedPopulation] using hp)
  have hselector := RootIndexed.childrenAtGeneration_isLowerFiniteBy_real
    n population field initial hdepth hweight
  have hselectedLeft := RootIndexed.selectedPopulationTotalized_succ_spec
    N Finset.univ initial id id n field hselector
  have hselectedRight := infiniteOffspringFirstN_spec
    (selectedPopulationRankPosition N n initial field) batch hgood.finiteWeight
  have hcardLeft := rankedPopulation_succ_card_of_good
    N n initial field hcard hgood
  have hcardRight := infiniteOffspringFirstN_card
    (selectedPopulationRankPosition N n initial field) batch hgood
  have himage : Set.image (rankedChildAddress N n initial field) candidatesRight =
      candidatesLeft := by
    simpa [batch, candidatesLeft, candidatesRight, population,
      rankedRoots, rankedPopulation] using
      rankedChildAddress_candidateImage N n initial field hcard
  have hN : 0 < N := Nat.pos_of_ne_zero (by
    intro h
    subst N
    exact Fin.elim0 i)
  let fallback : InfiniteSlotLabel N := (⟨0, hN⟩, 0)
  let backward : RootIndexed.TreeNode (Fin N) ℕ → InfiniteSlotLabel N := fun p =>
    if hp : p ∈ candidatesLeft then
      Classical.choose ((Set.mem_image (rankedChildAddress N n initial field)
        candidatesRight p).mp (by rw [himage]; exact hp))
    else fallback
  have hinverse (p : RootIndexed.TreeNode (Fin N) ℕ) (hp : p ∈ candidatesLeft) :
      backward p ∈ candidatesRight ∧
        rankedChildAddress N n initial field (backward p) = p := by
    simpa [backward, hp] using
      (Classical.choose_spec ((Set.mem_image (rankedChildAddress N n initial field)
        candidatesRight p).mp (by rw [himage]; exact hp)))
  have hforward : ∀ q ∈ candidatesRight,
      rankedChildAddress N n initial field q ∈ candidatesLeft := by
    intro q hq
    have hmem : rankedChildAddress N n initial field q ∈
        Set.image (rankedChildAddress N n initial field) candidatesRight :=
      Set.mem_image_of_mem _ hq
    rw [himage] at hmem
    exact hmem
  have hbackward : ∀ p ∈ candidatesLeft, backward p ∈ candidatesRight := by
    intro p hp
    exact (hinverse p hp).1
  have hbackwardForward : ∀ p ∈ candidatesLeft,
      rankedChildAddress N n initial field (backward p) = p := by
    intro p hp
    exact (hinverse p hp).2
  have hforwardBackward : ∀ q ∈ candidatesRight,
      backward (rankedChildAddress N n initial field q) = q := by
    intro q hq
    apply rankedChildAddress_injective N n initial field
    exact (hinverse (rankedChildAddress N n initial field q) (hforward q hq)).2
  have hvalue : ∀ q ∈ candidatesRight,
      valueLeft (rankedChildAddress N n initial field q) = valueRight q := by
    intro q _
    let slot := ofLex q
    let root := roots slot.1
    have hrootDepth : (roots slot.1).2.length = n := by
      simpa [roots, rankedRoots, selectedPopulationRankRoots, slot] using
        selectedPopulationRankRoot_depth N n initial field slot.1
    have hrootDepth' :
        (selectedPopulationRankRoots N initial n field slot.1).2.length = n := by
      simpa [roots, rankedRoots, slot] using hrootDepth
    have hchildDepth : (rankedChildAddress N n initial field q).2.length = n + 1 := by
      change ((roots slot.1).2 ++ [slot.2]).length = n + 1
      rw [List.length_append, hrootDepth]
      simp
    change RootIndexed.observedPositionAtGeneration initial id id (n + 1) field
        (rankedChildAddress N n initial field q) =
      infiniteOffspringPosition (selectedPopulationRankPosition N n initial field) batch q
    rw [RootIndexed.observedPositionAtGeneration_eq initial id id
      (n + 1) field (rankedChildAddress N n initial field q) hchildDepth]
    have hstep := Combinatorics.Branching.RootIndexed.BranchingWalk.position_child id
      (Combinatorics.Branching.RootIndexed.BranchingWalk.ofStepField initial field)
      root.1 root.2 slot.2
    simpa [rankedChildAddress, infiniteOffspringPosition, selectedPopulationRankPosition,
      rankedRoots, roots, batch,
      rankedRoot_batch_value, slot, root, RootIndexed.observedPositionAtGeneration,
      RootIndexed.positionAtGeneration, RootIndexed.position, RootIndexed.displace,
      hrootDepth,
      hrootDepth'] using hstep
  have hcounts : ∀ a : ℝ,
      (selectedLeft.filter fun p => valueLeft p ≤ a).card =
        (selectedRight.filter fun q => valueRight q ≤ a).card := by
    intro a
    exact firstNBy_value_thresholdCounts_eq_of_bijectiveCandidates
      valueLeft valueRight candidatesLeft candidatesRight selectedLeft selectedRight
      hselectedLeft hselectedRight hcardLeft hcardRight
      (rankedChildAddress N n initial field) backward
      hforward hbackward hbackwardForward hforwardBackward hvalue a
  let fallbackLeft : RootIndexed.TreeNode (Fin N) ℕ :=
    (i, List.replicate (n + 1) 0)
  let fallbackRight : InfiniteSlotLabel N := fallback
  have hrankValues := selectedRankValue_eq_of_thresholdCounts
    valueLeft valueRight selectedLeft selectedRight fallbackLeft fallbackRight
    hcardLeft hcardRight hcounts i
  have hleft : selectedPopulationRankPosition N (n + 1) initial field i =
      selectedRankValue valueLeft selectedLeft fallbackLeft i.val := by
    have hfull : (RootIndexed.selectedPopulationTotalized N Finset.univ
        initial id id (n + 1) field).card = N := by
      simpa [rankedPopulation] using hcardLeft
    change RootIndexed.observedPositionAtGeneration initial id id (n + 1) field
        (rankedRoots N (n + 1) initial field i) =
      selectedRankValue valueLeft selectedLeft fallbackLeft i.val
    simp [rankedRoots, selectedPopulationRankRoots, selectedPopulationRankRoot,
      selectedRankValue, selectedLeft, rankedPopulation, fallbackLeft, hfull, valueLeft]
  have hright : infiniteOffspringTransition (selectedPopulationRankPosition N n initial field)
      batch hgood i = selectedRankValue valueRight selectedRight fallbackRight i.val := by
    let opt := particleAtRankBy valueRight selectedRight i.val
    have hopt : opt ≠ none := by
      intro hnone
      have hle := particleAtRankBy_eq_none_iff.mp hnone
      rw [hcardRight] at hle
      exact (not_le_of_gt i.isLt) hle
    cases h : opt with
    | none => exact (hopt h).elim
    | some p =>
        simp [infiniteOffspringTransition, selectedLabelAtRank,
          selectedRankValue, selectedRight, valueRight, opt, h]
  calc
    selectedPopulationRankPosition N (n + 1) initial field i =
        selectedRankValue valueLeft selectedLeft fallbackLeft i.val := hleft
    _ = selectedRankValue valueRight selectedRight fallbackRight i.val := hrankValues
    _ = infiniteOffspringTransition (selectedPopulationRankPosition N n initial field) batch hgood i := hright.symm

/-- If every ranked batch is admissible, then the finite root-indexed
selection trajectory is exactly the ranked infinite-offspring recursion. -/
theorem selectedPopulationRankPosition_eq_infiniteOffspringRun
    (N : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ)
    (hgood : ∀ n, IsGoodInfiniteOffspringBatch
      (selectedRootBatch (selectedPopulationRankRoots N initial) n field)) :
    ∀ n, selectedPopulationRankPosition N n initial field =
      infiniteOffspringRun
        (fun n => selectedRootBatch (selectedPopulationRankRoots N initial) n field)
        hgood (selectedPopulationRankPosition N 0 initial field) n := by
  have hcards := rankedPopulation_card_eq_of_rankedBatches_good
    N initial field hgood
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      funext i
      rw [rankedPosition_succ_eq_transition N n initial field (hcards n)
        (hgood n) i]
      rw [infiniteOffspringRun_succ, ← ih]

/-- If the selected ranked batches give the origin run its speed, the
root-indexed finite selection has that same speed from its ranked initial
population. -/
theorem selectedPopulationRankPosition_hasAsymptoticSpeed_of_originRun
    {N : ℕ} (hN : 0 < N) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ)
    (hgood : ∀ n, IsGoodInfiniteOffspringBatch
      (selectedRootBatch (selectedPopulationRankRoots N initial) n field))
    (c : ℝ)
    (horigin : Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
      (𝕜 := ℝ)
      (fun n => infiniteOffspringRun
        (fun n => selectedRootBatch (selectedPopulationRankRoots N initial) n field)
        hgood (fun _ => 0) n ⟨0, hN⟩) c) :
    Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
      (𝕜 := ℝ)
      (fun n => selectedPopulationRankPosition N n initial field ⟨0, hN⟩) c := by
  let offspring : ℕ → Fin N → Step ℕ ℝ :=
    fun n => selectedRootBatch (selectedPopulationRankRoots N initial) n field
  have hinitial := infiniteOffspringRun_rankZero_hasAsymptoticSpeed_of_initial
    hN offspring hgood (selectedPopulationRankPosition N 0 initial field) c (by
      simpa [offspring] using horigin)
  have htrajectory := selectedPopulationRankPosition_eq_infiniteOffspringRun
    N initial field hgood
  change Tendsto
    (fun n : ℕ => (n : ℝ)⁻¹ * selectedPopulationRankPosition N n initial field ⟨0, hN⟩)
    atTop (𝓝 c)
  apply hinitial.congr'
  filter_upwards [] with n
  rw [htrajectory n]
  rfl

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

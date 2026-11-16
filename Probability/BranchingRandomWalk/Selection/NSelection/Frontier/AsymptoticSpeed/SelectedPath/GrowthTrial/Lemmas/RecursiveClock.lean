/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Causal
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Recursive
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Splits

/-!
# Recursive failures within the selected-path clock

## Internal proof declarations

* `rawSplitTime_eq_of_first_sampled_split` and
  `first_sampled_split_of_rawSplitTime_eq` identify the population's raw split
  index with the first split mark on the selected path.
* `firstSplitRoots_eq_of_rawSplitTime_eq` identifies the two sibling addresses
  at the first sampled split.
* `splitCount_add_after_first_split` splits the count into the first split and
  the count in its continuation subtree.
* `mem_recursiveFailure_of_no_success`: if at least $K$ live splits occur
  before $n$ and their growth trials all fail, the root field belongs to the
  $K$-fold recursive failure event.

This identifies the recursive trials with the trials on the same pre-sampled
path in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with
Infinite Offspring* (Fudan University, 2026), Chapter 4, Theorem 1.1 at $a=0$.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial

open Combinatorics.Branching Combinatorics.UlamHarris
open Combinatorics.Branching.Step.FiniteSelection
open Combinatorics.Branching.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath
open ProbabilityTheory.BranchingRandomWalk.Selection.Stepwise.SplitTime

private lemma population_eq_singleton_before_split
    {Root α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (ω : RootIndexed.StepField Root α X)
    (k : ℕ) (hne : ∀ u, (R (ω r u)).Nonempty)
    (hearly : ∀ j < k, ¬ splitEvent R r j ω) :
    ∀ j ≤ k, Selection.Stepwise.population R j (ω r) = {selectedPath R r j ω} := by
  classical
  intro j
  induction j with
  | zero => intro; rfl
  | succ j ih =>
    intro hj
    have hcard : (R (ω r (selectedPath R r j ω))).card = 1 := by
      have hpos := Finset.card_pos.mpr (hne (selectedPath R r j ω))
      have hnot := hearly j (by omega)
      change ¬ 2 ≤ (R (ω r (selectedPath R r j ω))).card at hnot
      omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
    have hmem := continuationSlot_mem_of_selected_nonempty R
      (ω r (selectedPath R r j ω)) (hne _)
    rw [hi] at hmem
    have hslot := Finset.mem_singleton.mp hmem
    rw [Selection.Stepwise.population_succ, ih (by omega), selectedPath, hslot]
    simp [Selection.Stepwise.grow, Selection.Stepwise.children, frontierMarks, hi, depth]

lemma rawSplitTime_eq_of_first_sampled_split
    {Root α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (ω : RootIndexed.StepField Root α X)
    (k : ℕ) (hne : ∀ u, (R (ω r u)).Nonempty)
    (hs : splitEvent R r k ω) (hearly : ∀ j < k, ¬ splitEvent R r j ω) :
    selectedPopulationRawSplitTime R (ω r) = k := by
  classical
  have hpop := population_eq_singleton_before_split R r ω k hne hearly
  apply (firstDeclaredSuccess_eq_iff (selectedPopulationSplitDeclaration R) (ω r) k).2
  constructor
  · change 2 ≤ (Selection.Stepwise.population R (k + 1) (ω r)).card
    rw [Selection.Stepwise.population_succ, hpop k le_rfl]
    change 2 ≤ (R (ω r (selectedPath R r k ω))).card at hs
    have hinj : Function.Injective (fun i : α => selectedPath R r k ω ++ [i]) := by
      intro i j hij
      exact List.singleton_injective (List.append_right_injective _ hij)
    simp only [Selection.Stepwise.grow, Finset.singleton_biUnion, Selection.Stepwise.children,
      frontierMarks, depth, ite_true]
    calc
      2 ≤ (R (ω r (selectedPath R r k ω))).card := hs
      _ = _ := by
        symm
        convert! Finset.card_image_of_injective (R (ω r (selectedPath R r k ω))) hinj
  · intro j hj
    change ¬ 2 ≤ (Selection.Stepwise.population R (j + 1) (ω r)).card
    rw [hpop _ (by omega)]
    simp

lemma first_sampled_split_of_rawSplitTime_eq
    {Root α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (ω : RootIndexed.StepField Root α X)
    (k : ℕ) (hne : ∀ u, (R (ω r u)).Nonempty)
    (hraw : selectedPopulationRawSplitTime R (ω r) = k) :
    splitEvent R r k ω ∧ ∀ j < k, ¬ splitEvent R r j ω := by
  classical
  have hdecl := (firstDeclaredSuccess_eq_iff (selectedPopulationSplitDeclaration R) (ω r) k).mp hraw
  have hearly : ∀ j < k, ¬ splitEvent R r j ω := by
    intro j hj hs
    have hex : ∃ i, i < k ∧ splitEvent R r i ω := ⟨j, hj, hs⟩
    let i := Nat.find hex
    have hi := Nat.find_spec hex
    have hmin (l : ℕ) (hl : l < i) (hs' : splitEvent R r l ω) : False :=
      Nat.find_min hex hl ⟨hl.trans hi.1, hs'⟩
    have heq := rawSplitTime_eq_of_first_sampled_split R r ω i hne hi.2 hmin
    have : i = k := WithTop.coe_injective (heq.symm.trans hraw)
    omega
  refine ⟨?_, hearly⟩
  by_contra hs
  have hall (j : ℕ) (hj : j < k + 1) : ¬ splitEvent R r j ω := by
    by_cases hjk : j < k
    · exact hearly j hjk
    · rwa [show j = k by omega]
  have hpop := population_eq_singleton_before_split R r ω (k + 1) hne hall (k + 1) le_rfl
  have hcard := hdecl.1
  change 2 ≤ (Selection.Stepwise.population R (k + 1) (ω r)).card at hcard
  rw [hpop] at hcard
  simp at hcard

lemma firstSplitRoots_eq_of_rawSplitTime_eq
    {Root α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (ω : RootIndexed.StepField Root α X)
    (k : ℕ) (hne : ∀ u, (R (ω r u)).Nonempty)
    (hraw : selectedPopulationRawSplitTime R (ω r) = k) :
    let p := selectedPath R r k ω
    let ξ := ω r p
    selectedPopulationFirstSplitRoots R (ω r) 0 = p ++ [firstSelectedSlot R ξ] ∧
      selectedPopulationFirstSplitRoots R (ω r) 1 = p ++ [secondSelectedSlot R ξ] := by
  classical
  obtain ⟨_, hearly⟩ := first_sampled_split_of_rawSplitTime_eq R r ω k hne hraw
  have hpop := population_eq_singleton_before_split R r ω k hne hearly
  simp [selectedPopulationFirstSplitRoots, hraw, selectedChildrenAtFirstSplit, hpop k le_rfl]

private lemma firstSplitSubtrees_eq
    {Root α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (ω : RootIndexed.StepField Root α X)
    (k : ℕ) (hne : ∀ u, (R (ω r u)).Nonempty)
    (hs : splitEvent R r k ω) (hearly : ∀ j < k, ¬ splitEvent R r j ω) :
    let p := selectedPath R r k ω
    let mark := ω r p
    selectedPopulationFirstSplitSubtrees R (ω r) 0 =
      (fun v => ω r ((p ++ [firstSelectedSlot R mark]) ++ v)) ∧
    selectedPopulationFirstSplitSubtrees R (ω r) 1 =
      continuationFieldAtSplit R r k ω PUnit.unit := by
  classical
  have hpop := population_eq_singleton_before_split R r ω k hne hearly
  have hraw := rawSplitTime_eq_of_first_sampled_split R r ω k hne hs hearly
  simp [selectedPopulationFirstSplitSubtrees, selectedPopulationFirstSplitRoots, hraw,
    selectedChildrenAtFirstSplit, hpop k le_rfl, selectedSubtreeStepFieldVector,
    subtreeStepFieldVector]
  constructor
  · unfold ProbabilityTheory.BranchingRandomWalk.subtreeStepField
    simp only [List.append_assoc, List.singleton_append]
  · unfold ProbabilityTheory.BranchingRandomWalk.subtreeStepField continuationFieldAtSplit
    rw [continuationPrefix]

lemma splitCount_add_after_first_split
    {Root α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (ω : RootIndexed.StepField Root α X)
    (k m : ℕ) (halive : isAlive R r k ω)
    (hs : splitEvent R r k ω) (hearly : ∀ j < k, ¬ splitEvent R r j ω) :
    splitCount R r (k + 1 + m) ω =
      1 + splitCount R PUnit.unit m (continuationFieldAtSplit R r k ω) := by
  classical
  rw [splitCount_eq_sum_indicators, splitCount_eq_sum_indicators, Finset.sum_range_add]
  have hpre : (∑ j ∈ Finset.range (k + 1),
      if isAlive R r j ω ∧ splitEvent R r j ω then 1 else 0) = 1 := by
    rw [Finset.sum_range_succ]
    have hz : (∑ j ∈ Finset.range k,
        if isAlive R r j ω ∧ splitEvent R r j ω then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun j hj => by simp [hearly j (Finset.mem_range.mp hj)]
    simp [hz, halive, hs]
  rw [hpre]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [isAlive_decompose_at_split_field R r k ω halive hs j]
  have hmark := mark_decompose_at_split_field R r k j ω hs
  change (if isAlive R PUnit.unit j (continuationFieldAtSplit R r k ω) ∧
    ω r (selectedPath R r (k + 1 + j) ω) ∈ splitBy R then 1 else 0) = _
  rw [hmark]
  rfl

lemma mem_recursiveFailure_of_no_success
    {Root : Type} {α X : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (lower upper duration K : ℕ) (r : Root) (ω : RootIndexed.StepField Root α X)
    (hne : ∀ u, (R (ω r u)).Nonempty) (n : ℕ)
    (hcount : K ≤ splitCount R r n ω)
    (hfail : ∀ j < n, ω ∉ successEvent R growth hR lower upper duration r j) :
    ω r ∈ recursiveFailure R growth duration lower upper K := by
  classical
  induction K generalizing Root r ω n with
  | zero => exact Set.mem_univ _
  | succ K ih =>
    have halive : ∀ j, isAlive R r j ω := by
      intro j
      induction j with
      | zero => trivial
      | succ j ih => exact ⟨ih, hne _⟩
    have hex : ∃ j, j < n ∧ splitEvent R r j ω := by
      have hpos : 0 < splitCount R r n ω := by omega
      change 0 < ((Finset.range n).filter fun j =>
        isAlive R r j ω ∧ splitEvent R r j ω).card at hpos
      obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      exact ⟨j, hj.1, hj.2.2⟩
    let k := Nat.find hex
    have hk : k < n := (Nat.find_spec hex).1
    have hs : splitEvent R r k ω := (Nat.find_spec hex).2
    have hearly : ∀ j < k, ¬ splitEvent R r j ω :=
      fun j hj h => Nat.find_min hex hj ⟨hj.trans hk, h⟩
    let tail := continuationFieldAtSplit R r k ω
    have htailCount : K ≤ splitCount R PUnit.unit (n - (k + 1)) tail := by
      have heq : splitCount R r n ω =
          1 + splitCount R PUnit.unit (n - (k + 1)) tail := by
        conv_lhs => rw [show n = k + 1 + (n - (k + 1)) by omega]
        exact splitCount_add_after_first_split R r ω k _ (halive k) hs hearly
      omega
    have htailFail (j : ℕ) (hj : j < n - (k + 1)) :
        tail ∉ successEvent R growth hR lower upper duration PUnit.unit j := by
      intro h
      apply hfail (k + 1 + j) (by omega)
      rcases h with ⟨hAlive, hSplit, hTrial⟩
      have hroot := (root_at_recursive_split R hR r k j ω (halive k) hs hAlive hSplit)
      refine ⟨hroot.2.1, ?_, ?_⟩
      · change ω r (selectedPath R r (k + 1 + j) ω) ∈ splitBy R
        rw [mark_decompose_at_split_field R r k j ω hs]
        exact hSplit
      · convert hTrial using 2
        funext v
        rw [hroot.1, (root_at_split R hR PUnit.unit j tail hSplit).1]
        simp [tail, continuationFieldAtSplit, List.append_assoc]
    obtain ⟨hfirst, hsecond⟩ := firstSplitSubtrees_eq R r ω k hne hs hearly
    change ¬ growthTrialSuccess growth lower upper duration
      (selectedPopulationFirstSplitSubtrees R (ω r) 0) ∧
        selectedPopulationFirstSplitSubtrees R (ω r) 1 ∈
          recursiveFailure R growth duration lower upper K
    constructor
    · rw [hfirst]
      intro h
      apply hfail k hk
      refine ⟨halive k, hs, ?_⟩
      rwa [(root_at_split R hR r k ω hs).1]
    · rw [hsecond]
      exact ih PUnit.unit tail (fun _ => hne _) _ htailCount htailFail

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial

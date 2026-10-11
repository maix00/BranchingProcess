/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Speed.InitialPopulationTrajectory
import Probability.BranchingRandomWalk.Selection.NSelection.Speed.SelectedPopulationBatch
import Probability.BranchingRandomWalk.Selection.NSelection.Speed.KingmanInterface
import Probability.Sequence.IID.Law

/-!
# Ranked batches and finite-selection speed

This file identifies the law of the offspring batches read at the spatially
ranked particles. It also compares finite selected values when their
tie-breaking label orders differ, by using counts below each value threshold.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.UlamHarris
open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed

/-- The offspring batches read from the spatially ranked population form an
i.i.d. generation environment with the exact-`N` law. -/
theorem selectedPopulationRankBatch_hasLaw_generationEnvironment
    (N : ℕ) (initial : Fin N → ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin N) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (Fin N × TreeNode ℕ)]
    [MeasurableSingletonClass (Fin N → Fin N × TreeNode ℕ)]
    [Countable (Fin N × TreeNode ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] :
    HasLaw
      (fun field n => selectedRootBatch
        (selectedPopulationRankRoots N initial) n field)
      (generationEnvironmentLaw μ N)
      (RootIndexed.stepFieldLaw (Root := Fin N) μ) := by
  classical
  let chosen := selectedPopulationRankRoots N initial
  let P := RootIndexed.stepFieldLaw (Root := Fin N) μ
  have hcount : ∀ n, (Set.range (chosen n)).Countable := by
    intro n
    exact selectedPopulationRankRoots_countable N n initial
  have hfiber : ∀ n roots, MeasurableSet[
      RootIndexed.stepFiltration (Root := Fin N) (α := ℕ) (X := ℝ) n]
      {field | chosen n field = roots} := by
    intro n roots
    exact selectedPopulationRankRoots_fiber_measurable N n initial roots
  have hdepth : ∀ n field i, (chosen n field i).2.length = n := by
    intro n field i
    exact selectedPopulationRankRoot_depth N n initial field i
  have hinj : ∀ n field, Function.Injective (chosen n field) := by
    intro n field
    exact selectedPopulationRankRoots_injective N n initial field
  have hindep : iIndepFun (selectedRootBatch chosen ·) P := by
    exact selectedPopulationRankBatch_iIndepFun N initial μ
  have hmeasAt := RootIndexed.measurable_selectedRootBatch_at_succ
    chosen hcount hfiber hdepth
  have hmeas (n : ℕ) : Measurable (selectedRootBatch chosen n) := by
    let F := RootIndexed.stepFiltration (Root := Fin N) (α := ℕ) (X := ℝ)
    exact (hmeasAt n).mono (F.le (n + 1)) le_rfl
  have hlaw (n : ℕ) : HasLaw (selectedRootBatch chosen n)
      (generationBatchLaw μ N) P := by
    refine ⟨(hmeas n).aemeasurable, ?_⟩
    simpa [P, chosen, generationBatchLaw] using
      (RootIndexed.selectedRootBatch_independent_and_law μ chosen
        hcount hfiber hdepth hinj n).2
  have hsequence := ProbabilityTheory.iIndepFun.hasLaw_iidSequenceLaw
    hindep hmeas hlaw
  simpa [generationEnvironmentLaw, generationBatchLaw,
    ProbabilityTheory.iidSequenceLaw] using hsequence

/-- The value at a prescribed rank in a finite selected set. The fallback is
irrelevant when the set has at least `k + 1` elements. -/
noncomputable def selectedRankValue
    {ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (value : ι → Value) (selected : Finset ι) (fallback : ι) (k : ℕ) : Value :=
  value ((Combinatorics.Branching.Selection.NSelection.particleAtRankBy
    value selected k).getD fallback)

private theorem selectedRankValue_threshold_bounds
    {ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (value : ι → Value) (selected : Finset ι) (fallback : ι)
    {N k : ℕ} (hcard : selected.card = N) (hk : k < N) :
    (selected.filter fun q => value q < selectedRankValue value selected fallback k).card ≤ k ∧
      k + 1 ≤ (selected.filter fun q =>
        value q ≤ selectedRankValue value selected fallback k).card := by
  let p := (Combinatorics.Branching.Selection.NSelection.particleAtRankBy
    value selected k).getD fallback
  have hnotNone : Combinatorics.Branching.Selection.NSelection.particleAtRankBy
      value selected k ≠ none := by
    intro hnone
    rw [Combinatorics.Branching.Selection.NSelection.particleAtRankBy_eq_none_iff] at hnone
    omega
  have hp : p ∈ selected ∧
      Combinatorics.Branching.Selection.NSelection.rankBy value selected p = k := by
    have hsome : Combinatorics.Branching.Selection.NSelection.particleAtRankBy
        value selected k = some p := by
      cases h : Combinatorics.Branching.Selection.NSelection.particleAtRankBy
          value selected k with
      | none => exact (hnotNone h).elim
      | some q => simp [p, h]
    exact Combinatorics.Branching.Selection.NSelection.particleAtRankBy_eq_some_iff.mp
      hsome
  have hkeyCard := hp.2
  unfold Combinatorics.Branching.Selection.NSelection.rankBy
    Combinatorics.Branching.Selection.NSelection.rank at hkeyCard
  rw [Finset.filter_image] at hkeyCard
  rw [Finset.card_image_of_injective _
    (Combinatorics.Branching.Selection.NSelection.valueKey_injective value)] at hkeyCard
  have hstrictSubset : (selected.filter fun q => value q < value p) ⊆
      selected.filter fun q =>
        Combinatorics.Branching.Selection.NSelection.valueKey value q <
          Combinatorics.Branching.Selection.NSelection.valueKey value p := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqin, hlt⟩
    exact Finset.mem_filter.mpr ⟨hqin, Prod.Lex.left q p hlt⟩
  have hstrictCard : (selected.filter fun q => value q < value p).card ≤ k := by
    calc
      (selected.filter fun q => value q < value p).card ≤
          (selected.filter fun q =>
            Combinatorics.Branching.Selection.NSelection.valueKey value q <
              Combinatorics.Branching.Selection.NSelection.valueKey value p).card :=
        Finset.card_le_card hstrictSubset
      _ = k := hkeyCard
  have hpNotKey : p ∉ selected.filter fun q =>
      Combinatorics.Branching.Selection.NSelection.valueKey value q <
        Combinatorics.Branching.Selection.NSelection.valueKey value p := by
    simp
  have hinsert : insert p (selected.filter fun q =>
      Combinatorics.Branching.Selection.NSelection.valueKey value q <
        Combinatorics.Branching.Selection.NSelection.valueKey value p) ⊆
      selected.filter fun q => value q ≤ value p := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_filter.mpr ⟨hp.1, le_rfl⟩
    · rcases Finset.mem_filter.mp hq with ⟨hqin, hkey⟩
      have hle : value q ≤ value p := by
        change Prod.Lex (· < ·) (· < ·) (value q, q) (value p, p) at hkey
        rcases Prod.Lex.lt_iff.mp hkey with hlt | ⟨heq, _⟩
        · exact le_of_lt hlt
        · exact heq.le
      exact Finset.mem_filter.mpr ⟨hqin, hle⟩
  have hleCard : k + 1 ≤ (selected.filter fun q => value q ≤ value p).card := by
    calc
      k + 1 = (insert p (selected.filter fun q =>
          Combinatorics.Branching.Selection.NSelection.valueKey value q <
            Combinatorics.Branching.Selection.NSelection.valueKey value p)).card := by
        rw [Finset.card_insert_of_notMem hpNotKey, hkeyCard]
      _ ≤ (selected.filter fun q => value q ≤ value p).card :=
        Finset.card_le_card hinsert
  constructor
  · have hvalue : selectedRankValue value selected fallback k = value p := rfl
    rw [hvalue]
    exact hstrictCard
  · have hvalue : selectedRankValue value selected fallback k = value p := rfl
    rw [hvalue]
    exact hleCard

/-- Finite selections with the same counts below every value threshold have
the same value at each rank, even when their tie-breaking label orders differ. -/
theorem selectedRankValue_eq_of_thresholdCounts
    {ι κ Value : Type*} [LinearOrder ι] [LinearOrder κ] [LinearOrder Value]
    {N : ℕ} (valueLeft : ι → Value) (valueRight : κ → Value)
    (selectedLeft : Finset ι) (selectedRight : Finset κ)
    (fallbackLeft : ι) (fallbackRight : κ)
    (hcardLeft : selectedLeft.card = N) (hcardRight : selectedRight.card = N)
    (hcounts : ∀ a : Value,
      (selectedLeft.filter fun q => valueLeft q ≤ a).card =
        (selectedRight.filter fun q => valueRight q ≤ a).card)
    (i : Fin N) :
    selectedRankValue valueLeft selectedLeft fallbackLeft i.val =
      selectedRankValue valueRight selectedRight fallbackRight i.val := by
  have hleft := selectedRankValue_threshold_bounds valueLeft selectedLeft fallbackLeft
    hcardLeft i.isLt
  have hright := selectedRankValue_threshold_bounds valueRight selectedRight fallbackRight
    hcardRight i.isLt
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hcountLeft := hcounts
      (selectedRankValue valueLeft selectedLeft fallbackLeft i.val)
    have hcountRightLe :
        (selectedRight.filter fun q => valueRight q ≤
          selectedRankValue valueLeft selectedLeft fallbackLeft i.val).card ≤ i.val := by
      calc
        (selectedRight.filter fun q => valueRight q ≤
            selectedRankValue valueLeft selectedLeft fallbackLeft i.val).card ≤
            (selectedRight.filter fun q => valueRight q <
              selectedRankValue valueRight selectedRight fallbackRight i.val).card := by
          apply Finset.card_le_card
          intro q hq
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,
            lt_of_le_of_lt (Finset.mem_filter.mp hq).2 hlt⟩
        _ ≤ i.val := hright.1
    have hcountLeftGe : i.val + 1 ≤
        (selectedLeft.filter fun q => valueLeft q ≤
          selectedRankValue valueLeft selectedLeft fallbackLeft i.val).card := hleft.2
    have hcontradiction : i.val + 1 ≤ i.val := by
      calc
        i.val + 1 ≤ (selectedLeft.filter fun q => valueLeft q ≤
            selectedRankValue valueLeft selectedLeft fallbackLeft i.val).card :=
          hcountLeftGe
        _ = (selectedRight.filter fun q => valueRight q ≤
            selectedRankValue valueLeft selectedLeft fallbackLeft i.val).card := hcountLeft
        _ ≤ i.val := hcountRightLe
    omega
  · have hcountRight := hcounts
      (selectedRankValue valueRight selectedRight fallbackRight i.val)
    have hcountLeftLe :
        (selectedLeft.filter fun q => valueLeft q ≤
          selectedRankValue valueRight selectedRight fallbackRight i.val).card ≤ i.val := by
      calc
        (selectedLeft.filter fun q => valueLeft q ≤
            selectedRankValue valueRight selectedRight fallbackRight i.val).card ≤
            (selectedLeft.filter fun q => valueLeft q <
              selectedRankValue valueLeft selectedLeft fallbackLeft i.val).card := by
          apply Finset.card_le_card
          intro q hq
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,
            lt_of_le_of_lt (Finset.mem_filter.mp hq).2 hgt⟩
        _ ≤ i.val := hleft.1
    have hcountRightGe : i.val + 1 ≤
        (selectedRight.filter fun q => valueRight q ≤
          selectedRankValue valueRight selectedRight fallbackRight i.val).card := hright.2
    have hcontradiction : i.val + 1 ≤ i.val := by
      calc
        i.val + 1 ≤ (selectedRight.filter fun q => valueRight q ≤
            selectedRankValue valueRight selectedRight fallbackRight i.val).card :=
          hcountRightGe
        _ = (selectedLeft.filter fun q => valueLeft q ≤
            selectedRankValue valueRight selectedRight fallbackRight i.val).card := hcountRight.symm
        _ ≤ i.val := hcountLeftLe
    omega

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

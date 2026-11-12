/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Restart.RootedTrial.Reserve.Causal
public import Probability.BranchingRandomWalk.Restart.RootedTrial.Reserve.Candidates
import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.CapStopped
import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.RootIndexed.CapStopped
/-!
# Binary growth bounds for parallel reserve trials

Each candidate grows forward from the generation where its split is
observable.  With at most two selected children per particle, its age-`h`
population is bounded by `2^h`, regardless of the cap used to stop the trial.
Only the most recent `duration + 1` candidates can be active at once, giving a
deterministic capacity bound for the selected reserve-spine BRW population.

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineCandidatePopulation_card_le_binary`
  bounds the active candidate population by $(d+1)2^d$ for duration $d$ when
  the growth rule has at most two selected children per particle.
* `ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineAndCandidates_card_le_binary`
  bounds the union of the live reserve spine and active candidates by
  $1+(d+1)2^d$.
* `ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartBRWPopulation_card_le_binary`
  gives the same $1+(d+1)2^d$ capacity bound for each finite slice of the full
  restarted reserve-spine BRW population.

The general $b^n$ growth bounds for cap-stopped populations belong to the
modules defining those populations.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris

attribute [local instance] Classical.propDecidable Classical.decEq

/-- At generation `n`, every active candidate has age at most `duration`.
The total number of candidate particles is therefore bounded by the number
of active windows times the largest binary trial generation. -/
theorem selectedReserveSpineCandidatePopulation_card_le_binary
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (duration : ℕ) (hgrowth : growth.IsBoundedBy 2) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    (selectedReserveSpineCandidatePopulation R growth hR (2 ^ duration)
      duration r n ω).card ≤
      (duration + 1) * 2 ^ duration := by
  let enabled := selectedReserveSpineCandidateEnabled R r duration n ω
  let start : ℕ → RootIndexed.StepField Root α X → WithTop ℕ :=
    fun i _ => ((i + 1 : ℕ) : WithTop ℕ)
  let candidate : ℕ → ℕ → ℕ → RootIndexed.StepField Root α X →
      Finset (RootIndexed.TreeNode Root α) :=
    fun _ k age field =>
      (selectedReserveSpineLineages R hR).capStoppedCandidate
        R growth (2 ^ duration) r PUnit.unit k age field
  have hsum := ProbabilityTheory.Process.Stopping.Concurrent.Finite.population_card_le_sum
    (fun t field => selectedReserveSpineCandidateEnabled R r duration t field)
    start candidate n ω
  have hcomponent : ∀ i ∈ enabled,
      (ProbabilityTheory.Process.Stopping.Concurrent.Finite.component start candidate i n ω).card ≤
        2 ^ duration := by
    intro i hi
    have hi' : i < n ∧ n ≤ i + 1 + duration := by
      have hiEnabled : i ∈ selectedReserveSpineCandidateEnabled R r duration n ω := by
        simpa [enabled] using hi
      simp only [selectedReserveSpineCandidateEnabled, Finset.mem_filter,
        Finset.mem_range] at hiEnabled
      exact ⟨hiEnabled.1, hiEnabled.2.2.2⟩
    have hstart : start i ω = ((i + 1 : ℕ) : WithTop ℕ) := rfl
    have hage : n - (i + 1) ≤ duration := by omega
    rw [ProbabilityTheory.Process.Stopping.Concurrent.Finite.component_eq_of_start start candidate i ω
      (by omega) hstart]
    change ((selectedReserveSpineLineages R hR).capStoppedCandidate
      R growth (2 ^ duration) r PUnit.unit (i + 1) (n - (i + 1)) ω).card ≤ _
    simpa only [RootIndexed.ReserveLineages.capStoppedCandidate] using
      (rootedCapStoppedPopulation_card_le_pow growth (2 ^ duration) 2 hgrowth ω
        ((selectedReserveSpineLineages R hR).firstChildRootAt
          R r PUnit.unit (i + 1) ω) (n - (i + 1))).trans
        (Nat.pow_le_pow_right (by decide) hage)
  calc
    (selectedReserveSpineCandidatePopulation R growth hR (2 ^ duration)
        duration r n ω).card =
        (ProbabilityTheory.Process.Stopping.Concurrent.Finite.population
          (fun t field => selectedReserveSpineCandidateEnabled R r duration t field)
          start candidate n ω).card := by
      rfl
    _ ≤ ∑ i ∈ enabled,
        (ProbabilityTheory.Process.Stopping.Concurrent.Finite.component start candidate i n ω).card := hsum
    _ ≤ ∑ _i ∈ enabled, 2 ^ duration := by
      apply Finset.sum_le_sum
      intro i hi
      exact hcomponent i hi
    _ = enabled.card * 2 ^ duration := by simp
    _ ≤ (duration + 1) * 2 ^ duration := by
      exact Nat.mul_le_mul_right _
        (selectedReserveSpineCandidateEnabled_card_le R r duration n ω)

/-- The causal reserve spine and all currently active binary trials have the
deterministic capacity bound `1 + (duration + 1) * 2^duration`.  This bound
does not depend on trial outcomes or on an offspring-count moment. -/
theorem selectedReserveSpineAndCandidates_card_le_binary
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (duration : ℕ) (hgrowth : growth.IsBoundedBy 2) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    ((if selectedReserveSpineAlive R r n ω then
        ({(r, selectedReserveSpinePath R r n ω)} : Finset
          (RootIndexed.TreeNode Root α)) else ∅) ∪
      selectedReserveSpineCandidatePopulation R growth hR (2 ^ duration)
        duration r n ω).card ≤
      1 + (duration + 1) * 2 ^ duration := by
  calc
    _ ≤ (if selectedReserveSpineAlive R r n ω then
          ({(r, selectedReserveSpinePath R r n ω)} : Finset
            (RootIndexed.TreeNode Root α)) else ∅).card +
        (selectedReserveSpineCandidatePopulation R growth hR (2 ^ duration)
          duration r n ω).card :=
      Finset.card_union_le _ _
    _ ≤ 1 + (duration + 1) * 2 ^ duration := by
      refine Nat.add_le_add ?_
        (selectedReserveSpineCandidatePopulation_card_le_binary
          R growth hR duration hgrowth r n ω)
      by_cases h : selectedReserveSpineAlive R r n ω <;> simp [h]

/-- The same capacity bound for the finite causal-population wrapper. -/
theorem selectedReserveSpineRestartBRWPopulation_card_le_binary
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [MeasurableSpace Root]
    [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hgrowthMeas : Measurable growth.select) (duration : ℕ)
    (hgrowth : growth.IsBoundedBy 2) (r : Root)
    (hfinite :
      (selectedReserveSpineRestartBRWPopulation R growth hR hgrowthMeas
        (2 ^ duration) duration r).FiniteSlices)
    (n : ℕ) (ω : RootIndexed.StepField Root α X) :
    (hfinite.toFinset n ω).card ≤ 1 + (duration + 1) * 2 ^ duration := by
  have heq : hfinite.toFinset n ω =
      selectedReserveSpineRestartBRWPopulationSlice R growth hR (2 ^ duration)
        duration r n ω := by
    apply Finset.coe_injective
    rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
    rfl
  rw [heq]
  change ((if selectedReserveSpineAlive R r n ω then
      ({(r, selectedReserveSpinePath R r n ω)} : Finset
        (RootIndexed.TreeNode Root α)) else ∅) ∪
      selectedReserveSpineCandidatePopulation R growth hR (2 ^ duration)
        duration r n ω).card ≤ _
  exact selectedReserveSpineAndCandidates_card_le_binary
    R growth hR duration hgrowth r n ω

end ProbabilityTheory.BranchingRandomWalk

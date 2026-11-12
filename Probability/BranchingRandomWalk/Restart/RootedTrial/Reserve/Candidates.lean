/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Probability.BranchingRandomWalk.Restart.RootedTrial.Spine.ReservePath
public import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.RootIndexed.CapStopped
public import Probability.BranchingRandomWalk.Restart.Trial.RootIndexed
public import Probability.Process.Stopping.Concurrent.Finite

/-!
# Concurrent candidate populations along a reserve spine

## Public declarations

The declarations are selectedReserveSpineCandidateEnabled and
selectedReserveSpineCandidatePopulation,
selectedReserveSpineCandidateEnabled_card_le,
selectedReserveSpineCandidatePopulation_card_le, and
selectedReserveSpineAndCandidates_card_le. The enabled indices are
\[
  \{k<n:\;\operatorname{alive}(k),\;
    \operatorname{split}(k),\; n\le k+1+\mathrm{duration}\}.
\]
The population unions the corresponding root-indexed cap-stopped populations,
each started at time k+1. The cardinality results bound the total candidate population by the number
of active split generations and the cap on each candidate.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The candidate indices whose split has already been observed and whose
fixed growth window is still open.  The split at generation `k` is first
observable at generation `k + 1`; `k < n` enforces that adapted timing. -/
noncomputable def selectedReserveSpineCandidateEnabled
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (duration n : ℕ)
    (ω : RootIndexed.StepField Root α X) : Finset ℕ :=
  (Finset.range n).filter fun k =>
    selectedReserveSpineAlive R r k ω ∧
      (ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R) ∧
      n ≤ k + 1 + duration

/-- The finite concurrent family of cap-stopped first-child trials started
at every split along the pre-sampled reserve spine.  Each index is the
generation of its reserve parent, and its deterministic completion start is
the next generation. -/
noncomputable def selectedReserveSpineCandidatePopulation
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap duration : ℕ) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
  Finset (RootIndexed.TreeNode Root α) :=
  ProbabilityTheory.Process.Stopping.Concurrent.Finite.population
    (fun t ω => selectedReserveSpineCandidateEnabled R r duration t ω)
    (fun i _ => ((i + 1 : ℕ) : WithTop ℕ))
    (fun _i k age ω =>
      (selectedReserveSpineLineages R hR).capStoppedCandidate
        R growth cap r PUnit.unit k age ω)
    n ω

/-- A finite set of split-parent generations whose child candidates are
within `duration` generations of the current time has at most `duration + 1`
elements.  Send `k` to its remaining age `n - (k + 1)`. -/
private lemma card_le_of_generation_window
    {S : Finset ℕ} (n duration : ℕ)
    (hS : ∀ k ∈ S, k < n ∧ n ≤ k + 1 + duration) :
    S.card ≤ duration + 1 := by
  calc
    S.card ≤ (Finset.range (duration + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun k => n - (k + 1))
      · intro k hk
        have h := hS k hk
        have hremaining : n - (k + 1) ≤ duration :=
          Nat.sub_le_iff_le_add.mpr (by omega)
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hremaining)
      · intro a ha b hb hab
        have hka := hS a ha
        have hkb := hS b hb
        have hleft : a + 1 ≤ n := by omega
        have hright : b + 1 ≤ n := by omega
        have hsub : a + 1 = b + 1 :=
          tsub_inj_right hleft hright hab
        omega
    _ = duration + 1 := by simp

theorem selectedReserveSpineCandidateEnabled_card_le
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (duration n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    (selectedReserveSpineCandidateEnabled R r duration n ω).card ≤
      duration + 1 := by
  apply card_le_of_generation_window n duration
  intro k hk
  simp only [selectedReserveSpineCandidateEnabled, Finset.mem_filter,
    Finset.mem_range] at hk
  exact ⟨hk.1, hk.2.2.2⟩

/-- The concurrently active cap-stopped candidates occupy at most one
`2 * cap` slice per candidate index. -/
theorem selectedReserveSpineCandidatePopulation_card_le
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap duration : ℕ) (hgrowth : growth.IsBoundedBy 2)
    (hcap : 1 ≤ cap) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    (selectedReserveSpineCandidatePopulation R growth hR cap duration r n ω).card ≤
      (duration + 1) * (2 * cap) := by
  calc
    (selectedReserveSpineCandidatePopulation R growth hR cap duration r n ω).card ≤
        (selectedReserveSpineCandidateEnabled R r duration n ω).card * (2 * cap) := by
      change (ProbabilityTheory.Process.Stopping.Concurrent.Finite.population
        (fun t ω => selectedReserveSpineCandidateEnabled R r duration t ω)
        (fun i _ => ((i + 1 : ℕ) : WithTop ℕ))
        (fun i k age ω =>
          (selectedReserveSpineLineages R hR).capStoppedCandidate
            R growth cap r PUnit.unit k age ω)
        n ω).card ≤
          (selectedReserveSpineCandidateEnabled R r duration n ω).card * (2 * cap)
      apply ProbabilityTheory.Process.Stopping.Concurrent.Finite.population_card_le_enabled_mul_candidateCap
          (fun t ω => selectedReserveSpineCandidateEnabled R r duration t ω)
          (fun i _ => ((i + 1 : ℕ) : WithTop ℕ))
          (fun i k age ω =>
            (selectedReserveSpineLineages R hR).capStoppedCandidate
              R growth cap r PUnit.unit k age ω)
        (2 * cap) n ω
      intro i k age
      exact (selectedReserveSpineLineages R hR).capStoppedCandidate_card_le_two_mul
        R growth cap hgrowth hcap r i k age ω
    _ ≤ (duration + 1) * (2 * cap) :=
      Nat.mul_le_mul_right _
        (selectedReserveSpineCandidateEnabled_card_le R r duration n ω)

/-- The reserve spine together with the recent capped candidates obeys the
`1 + (duration + 1) * 2 * cap` capacity bound, pathwise. -/
theorem selectedReserveSpineAndCandidates_card_le
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap duration : ℕ) (hgrowth : growth.IsBoundedBy 2)
    (hcap : 1 ≤ cap) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    ((if selectedReserveSpineAlive R r n ω then
        ({(r, selectedReserveSpinePath R r n ω)} : Finset
          (RootIndexed.TreeNode Root α)) else ∅) ∪
      selectedReserveSpineCandidatePopulation R growth hR cap duration r n ω).card ≤
      1 + (duration + 1) * (2 * cap) := by
  calc
    ((if selectedReserveSpineAlive R r n ω then
        ({(r, selectedReserveSpinePath R r n ω)} : Finset
          (RootIndexed.TreeNode Root α)) else ∅) ∪
      selectedReserveSpineCandidatePopulation R growth hR cap duration r n ω).card ≤
        (if selectedReserveSpineAlive R r n ω then
          ({(r, selectedReserveSpinePath R r n ω)} : Finset
            (RootIndexed.TreeNode Root α)) else ∅).card +
          (selectedReserveSpineCandidatePopulation R growth hR cap duration r n ω).card :=
      Finset.card_union_le _ _
    _ ≤ 1 + (duration + 1) * (2 * cap) := by
      refine Nat.add_le_add ?_
        (selectedReserveSpineCandidatePopulation_card_le R growth hR cap duration
          hgrowth hcap r n ω)
      by_cases h : selectedReserveSpineAlive R r n ω <;> simp [h]

end ProbabilityTheory.BranchingRandomWalk

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Probability.BranchingRandomWalk.Restart.SelectedPath.Path
public import Probability.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Population.RootIndexed
public import Probability.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Roots
public import Probability.Process.Stopping.Concurrent.Finite

/-!
# Concurrent candidate populations along a selected path

## Public declarations

The public declarations are `Restart.SelectedPath.GrowthTrial.enabledIndices`,
`Restart.SelectedPath.GrowthTrial.population`,
`Restart.SelectedPath.GrowthTrial.enabledIndices_card_le`,
`Restart.SelectedPath.GrowthTrial.population_card_le`, and
`Restart.SelectedPath.Population.pathAndGrowthTrials_card_le`. The enabled indices are
\[
  \{k<n:\;\operatorname{alive}(k),\;
    \operatorname{split}(k),\; n\le k+1+\mathrm{duration}\}.
\]
The population unions the corresponding root-indexed cap-stopped populations,
each started at time `k + 1` from the first selected child. The cardinality results give the bounds
\[|E_n|\le d+1,\qquad |C_n|\le(d+1)(2c),\]
where `d` is the trial duration and `c` is the population cap.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The candidate indices whose split has already been observed and whose
fixed growth window is still open.  The split at generation `k` is first
observable at generation `k + 1`; `k < n` enforces that adapted timing. -/
noncomputable def GrowthTrial.enabledIndices
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (duration n : ℕ)
    (ω : RootIndexed.StepField Root α X) : Finset ℕ :=
  (Finset.range n).filter fun k =>
    Restart.SelectedPath.isAlive R r k ω ∧
      (Restart.SelectedPath.splitEvent R r k ω) ∧
      n ≤ k + 1 + duration

/-- The finite concurrent family of cap-stopped growth trial from the first selected child started
at every split along the pre-sampled selected path.  Each index is the
generation of its selected-path parent, and its deterministic completion start is
the next generation. -/
noncomputable def GrowthTrial.population
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap duration : ℕ) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
  Finset (RootIndexed.TreeNode Root α) :=
  ProbabilityTheory.Process.Stopping.Concurrent.Finite.population
    (fun t ω => Restart.SelectedPath.GrowthTrial.enabledIndices R r duration t ω)
    (fun i _ => ((i + 1 : ℕ) : WithTop ℕ))
    (fun _i k age ω =>
      Restart.SelectedPath.GrowthTrial.Population.capStoppedCandidate (Restart.SelectedPath.lineages R hR)
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

theorem GrowthTrial.enabledIndices_card_le
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (duration n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    (Restart.SelectedPath.GrowthTrial.enabledIndices R r duration n ω).card ≤
      duration + 1 := by
  apply card_le_of_generation_window n duration
  intro k hk
  simp only [Restart.SelectedPath.GrowthTrial.enabledIndices, Finset.mem_filter,
    Finset.mem_range] at hk
  exact ⟨hk.1, hk.2.2.2⟩

/-- The concurrently active cap-stopped candidates occupy at most one
`2 * cap` slice per candidate index. -/
theorem GrowthTrial.population_card_le
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap duration : ℕ) (hgrowth : growth.IsBoundedBy 2)
    (hcap : 1 ≤ cap) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    (Restart.SelectedPath.GrowthTrial.population R growth hR cap duration r n ω).card ≤
      (duration + 1) * (2 * cap) := by
  calc
    (Restart.SelectedPath.GrowthTrial.population R growth hR cap duration r n ω).card ≤
        (Restart.SelectedPath.GrowthTrial.enabledIndices R r duration n ω).card * (2 * cap) := by
      change (ProbabilityTheory.Process.Stopping.Concurrent.Finite.population
        (fun t ω => Restart.SelectedPath.GrowthTrial.enabledIndices R r duration t ω)
        (fun i _ => ((i + 1 : ℕ) : WithTop ℕ))
        (fun i k age ω =>
          Restart.SelectedPath.GrowthTrial.Population.capStoppedCandidate (Restart.SelectedPath.lineages R hR)
            R growth cap r PUnit.unit k age ω)
        n ω).card ≤
          (Restart.SelectedPath.GrowthTrial.enabledIndices R r duration n ω).card * (2 * cap)
      apply ProbabilityTheory.Process.Stopping.Concurrent.Finite.population_card_le_enabled_mul_candidateCap
          (fun t ω => Restart.SelectedPath.GrowthTrial.enabledIndices R r duration t ω)
          (fun i _ => ((i + 1 : ℕ) : WithTop ℕ))
          (fun i k age ω =>
            Restart.SelectedPath.GrowthTrial.Population.capStoppedCandidate (Restart.SelectedPath.lineages R hR)
              R growth cap r PUnit.unit k age ω)
        (2 * cap) n ω
      intro i k age
      exact Restart.SelectedPath.GrowthTrial.Population.capStoppedCandidate_card_le_two_mul (Restart.SelectedPath.lineages R hR)
        R growth cap hgrowth hcap r i k age ω
    _ ≤ (duration + 1) * (2 * cap) :=
      Nat.mul_le_mul_right _
        (Restart.SelectedPath.GrowthTrial.enabledIndices_card_le R r duration n ω)

/-- The selected path together with the recent capped candidates obeys the
`1 + (duration + 1) * 2 * cap` capacity bound, pathwise. -/
theorem Population.pathAndGrowthTrials_card_le
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap duration : ℕ) (hgrowth : growth.IsBoundedBy 2)
    (hcap : 1 ≤ cap) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    ((if Restart.SelectedPath.isAlive R r n ω then
        ({(r, Restart.selectedPath R r n ω)} : Finset
          (RootIndexed.TreeNode Root α)) else ∅) ∪
      Restart.SelectedPath.GrowthTrial.population R growth hR cap duration r n ω).card ≤
      1 + (duration + 1) * (2 * cap) := by
  calc
    ((if Restart.SelectedPath.isAlive R r n ω then
        ({(r, Restart.selectedPath R r n ω)} : Finset
          (RootIndexed.TreeNode Root α)) else ∅) ∪
      Restart.SelectedPath.GrowthTrial.population R growth hR cap duration r n ω).card ≤
        (if Restart.SelectedPath.isAlive R r n ω then
          ({(r, Restart.selectedPath R r n ω)} : Finset
            (RootIndexed.TreeNode Root α)) else ∅).card +
          (Restart.SelectedPath.GrowthTrial.population R growth hR cap duration r n ω).card :=
      Finset.card_union_le _ _
    _ ≤ 1 + (duration + 1) * (2 * cap) := by
      refine Nat.add_le_add ?_
        (Restart.SelectedPath.GrowthTrial.population_card_le R growth hR cap duration
          hgrowth hcap r n ω)
      by_cases h : Restart.SelectedPath.isAlive R r n ω <;> simp [h]

end ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath

end

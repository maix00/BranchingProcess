/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Processes.StepSelection.Concurrent
public import Probability.Process.HittingTime.Declarations

/-!
# Split schedules from selected root populations

Trial `i` uses its assigned pre-sampled root.  Starting from the observable
time of that trial, its selected population evolves by age.  The next trial
time is the first generation at which the current population reaches a fixed
cardinality threshold.  Every time is defined independently of trial success.

Countability of child slots is localized to observing the cardinality of the
finite Ulam--Harris population.  The underlying root family and all fixed
coordinate measurability results remain unrestricted.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed
namespace StepSelection
namespace SplitSchedule

open Combinatorics.UlamHarris Combinatorics.Branching

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The age-indexed, unlabelled selected population assigned to trial `i`. -/
noncomputable def candidate
    {Root α X : Type*} (R : Step.FiniteSelection α X)
    (root : ℕ → Root) (i : ℕ) (_start age : ℕ)
    (ω : RootIndexed.StepField Root α X) : Finset (TreeNode α) :=
  RootIndexed.StepSelection.population R age ω (root i)

/-- One trial population embedded into the global clock at `start`. -/
noncomputable def component
    {Root α X : Type*}
    (start : RootIndexed.StepField Root α X → WithTop ℕ)
    (R : Step.FiniteSelection α X) (root : ℕ → Root)
    (i n : ℕ) (ω : RootIndexed.StepField Root α X) :
    Finset (TreeNode α) :=
  ProbabilityTheory.BranchingRandomWalk.Concurrent.Finite.component
    (fun _ : Unit => start) (fun _ : Unit => candidate R root i)
    () n ω

theorem candidate_adapted
    {Root α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root) (i start age : ℕ) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) (start + age)]
      (candidate R root i start age) := by
  have h : Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) age]
      (candidate R root i start age) :=
    (measurable_pi_apply (root i)).comp
      (RootIndexed.StepSelection.population_adapted R hR age)
  exact h.mono
    ((RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)).mono
      (Nat.le_add_left age start)) le_rfl

theorem component_adapted
    {Root α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root) (i : ℕ)
    (start : RootIndexed.StepField Root α X → WithTop ℕ)
    (hstart : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) start) :
    ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (component start R root i n) := by
  intro n
  exact ProbabilityTheory.BranchingRandomWalk.Concurrent.Finite.component_adapted
    (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
    (fun _ : Unit => start) (fun _ => hstart)
    (fun _ : Unit => candidate R root i)
    (fun _ => candidate_adapted R hR root i) () n

/-- Recursive first-threshold times of the pre-sampled trial populations. -/
noncomputable def time
    {Root α X : Type*}
    (R : Step.FiniteSelection α X) (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (threshold : ℕ) :
    ℕ → RootIndexed.StepField Root α X → WithTop ℕ
  | 0 => initial
  | i + 1 => firstDeclaredSuccess fun n =>
      {ω | time R root initial threshold i ω ≤ n ∧
        threshold ≤
          (component (time R root initial threshold i) R root i n ω).card}

@[simp] theorem time_zero
    {Root α X : Type*}
    (R : Step.FiniteSelection α X) (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (threshold : ℕ) :
    time R root initial threshold 0 = initial :=
  rfl

@[simp] theorem time_succ
    {Root α X : Type*}
    (R : Step.FiniteSelection α X) (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (threshold i : ℕ) :
    time R root initial threshold (i + 1) =
      firstDeclaredSuccess fun n =>
        {ω | time R root initial threshold i ω ≤ n ∧
          threshold ≤
            (component (time R root initial threshold i) R root i n ω).card} :=
  rfl

/-- Each split time is a stopping time whenever the threshold observation is
measurable after any stopping start.  This is the abstract interface: it does
not impose countability on child labels or on the finite populations. -/
theorem time_isStoppingTime
    {Root α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (hinitial : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) initial)
    (threshold : ℕ)
    (hthreshold : ∀ i,
      IsStoppingTime
        (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
        (time R root initial threshold i) →
      ∀ n, MeasurableSet[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n]
        {ω | threshold ≤
          (component (time R root initial threshold i) R root i n ω).card}) :
    ∀ i, IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (time R root initial threshold i) := by
  intro i
  induction i with
  | zero => simpa using hinitial
  | succ i ih =>
      rw [time_succ]
      apply firstDeclaredSuccess_isStoppingTime
        (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      intro n
      exact (ih n).inter (hthreshold i ih n)

/-- Countable child labels make finite-population cardinality measurable and
hence discharge the abstract threshold-observation premise. -/
theorem time_isStoppingTime_of_countable
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (hinitial : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) initial)
    (threshold : ℕ) :
    ∀ i, IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (time R root initial threshold i) := by
  intro i
  induction i with
  | zero => simpa using hinitial
  | succ i ih =>
      rw [time_succ]
      apply firstDeclaredSuccess_isStoppingTime
        (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      intro n
      have hcomponent := component_adapted R hR root i
        (time R root initial threshold i) ih n
      have hcard : Measurable[RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) n]
          (fun ω => (component
            (time R root initial threshold i) R root i n ω).card) :=
        (measurable_of_countable
          (fun s : Finset (TreeNode α) => s.card)).comp hcomponent
      exact (ih n).inter (hcard measurableSet_Ici)

/-- The threshold schedule never starts a later trial before the current
one. -/
theorem time_le_succ
    {Root α X : Type*}
    (R : Step.FiniteSelection α X) (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (threshold i : ℕ) (ω : RootIndexed.StepField Root α X) :
    time R root initial threshold i ω ≤
      time R root initial threshold (i + 1) ω := by
  rw [time_succ]
  let declaration : ℕ → Set (RootIndexed.StepField Root α X) := fun n =>
    {ω | time R root initial threshold i ω ≤ n ∧
      threshold ≤
        (component (time R root initial threshold i) R root i n ω).card}
  change time R root initial threshold i ω ≤
    firstDeclaredSuccess declaration ω
  by_cases htop : firstDeclaredSuccess declaration ω = ⊤
  · simp [htop]
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
    have hdeclared := (firstDeclaredSuccess_le_iff declaration ω n).mp
      (by simp [← hn])
    obtain ⟨j, hjn, hj, _⟩ := hdeclared
    calc
      time R root initial threshold i ω ≤ (j : WithTop ℕ) := hj
      _ ≤ (n : WithTop ℕ) := WithTop.coe_le_coe.mpr hjn
      _ = firstDeclaredSuccess declaration ω := hn

theorem time_mono
    {Root α X : Type*}
    (R : Step.FiniteSelection α X) (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (threshold : ℕ) (ω : RootIndexed.StepField Root α X) :
    Monotone fun i => time R root initial threshold i ω := by
  apply monotone_nat_of_le_succ
  exact fun i => time_le_succ R root initial threshold i ω

/-- The labelled concurrent trial populations started by the split schedule
are adapted to the global generation domain flow. -/
theorem concurrentComponent_adapted
    {Root α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ) (threshold : ℕ)
    (htime : ∀ i, IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (time R root initial threshold i)) :
    ∀ i n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (Concurrent.component (time R root initial threshold) R root i n) := by
  apply Concurrent.component_adapted R hR root
  exact htime

theorem concurrentComponent_adapted_of_countable
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (hinitial : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) initial)
    (threshold : ℕ) :
    ∀ i n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (Concurrent.component (time R root initial threshold) R root i n) := by
  apply concurrentComponent_adapted R hR root initial threshold
  exact time_isStoppingTime_of_countable R hR root initial hinitial threshold

theorem concurrentPopulation_adapted
    {Root α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ) (threshold : ℕ)
    (htime : ∀ i, IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (time R root initial threshold i))
    (enabled : ℕ → RootIndexed.StepField Root α X → Finset ℕ)
    (henabled : ∀ n s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {ω | enabled n ω = s})
    (henabledRange : ∀ n, (Set.range (enabled n)).Countable) :
    ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (Concurrent.population enabled (time R root initial threshold)
        R root n) := by
  apply Concurrent.population_adapted R hR root enabled
    (time R root initial threshold) henabled henabledRange
  exact htime

theorem concurrentPopulation_adapted_of_countable
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (hinitial : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) initial)
    (threshold : ℕ)
    (enabled : ℕ → RootIndexed.StepField Root α X → Finset ℕ)
    (henabled : ∀ n s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {ω | enabled n ω = s})
    (henabledRange : ∀ n, (Set.range (enabled n)).Countable) :
    ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (Concurrent.population enabled (time R root initial threshold)
        R root n) := by
  apply concurrentPopulation_adapted R hR root initial threshold
    (time_isStoppingTime_of_countable R hR root initial hinitial threshold)
    enabled henabled henabledRange

end SplitSchedule
end StepSelection
end RootIndexed
end ProbabilityTheory.BranchingRandomWalk

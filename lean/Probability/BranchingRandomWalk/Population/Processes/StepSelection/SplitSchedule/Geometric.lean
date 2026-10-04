/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Law
public import Probability.BranchingRandomWalk.Timing.GeometricTrial

/-!
# Geometric law of independent split trials

The first successful fixed-age trial is defined from the root-indexed
pre-sampled field. Injective root assignment makes its zero-based index
geometric. This file only concerns trial outcomes; their causal global-clock
completion times are handled separately by `Completion` and `Success`.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed
namespace StepSelection
namespace SplitSchedule

open Combinatorics.UlamHarris Combinatorics.Branching

/-- Zero-based index of the first fixed-age selected population that reaches
the target, or `⊤` when no trial succeeds. -/
noncomputable def firstSuccess
    {Root α X : Type*} (R : Step.FiniteSelection α X)
    (root : ℕ → Root) (duration target : ℕ) :
    RootIndexed.StepField Root α X → WithTop ℕ :=
  firstDeclaredSuccess (successEvent R root duration target)

theorem firstSuccess_eq_iff
    {Root α X : Type*} (R : Step.FiniteSelection α X)
    (root : ℕ → Root) (duration target k : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    firstSuccess R root duration target ω = k ↔
      target ≤ (RootIndexed.StepSelection.population
        R duration ω (root k)).card ∧
      ∀ i < k, ¬ target ≤
        (RootIndexed.StepSelection.population R duration ω (root i)).card := by
  simpa [firstSuccess, successEvent] using
    firstDeclaredSuccess_eq_iff
      (successEvent R root duration target) ω k

/-- A finite first-success index is already determined by the generation
`duration` domain flow across all pre-sampled roots.  The root type itself is
unrestricted. -/
theorem measurableSet_firstSuccess_eq_adapted
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root) (duration target k : ℕ) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) duration]
      {ω | firstSuccess R root duration target ω = k} := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α X) :=
    RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) duration
  exact measurableSet_firstDeclaredSuccess_eq
    (fun i => measurableSet_successEvent_adapted
      R hR root duration target i) k

/-- Failure of every trial is also visible at generation `duration`.  The
countable union here concerns the `ℕ`-indexed trial clock, not the root or
offspring types. -/
theorem measurableSet_firstSuccess_eq_top_adapted
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root) (duration target : ℕ) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) duration]
      {ω | firstSuccess R root duration target ω = ⊤} := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α X) :=
    RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) duration
  exact measurableSet_firstDeclaredSuccess_eq_top
    (fun i => measurableSet_successEvent_adapted
      R hR root duration target i)

/-- The first successful trial has the geometric point probabilities
`p(1-p)^k`, with zero-based indexing. -/
theorem measure_firstSuccess_eq
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root) (hroot : Function.Injective root)
    (duration target : ℕ) (μ : Measure (Step α X))
    [IsProbabilityMeasure μ] (k : ℕ) :
    RootIndexed.stepFieldLaw (Root := Root) μ
        {ω | firstSuccess R root duration target ω = k} =
      ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
          (α := α) μ (successSet R duration target) *
        (1 - ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
          (α := α) μ (successSet R duration target)) ^ k := by
  apply measure_firstDeclaredSuccess_eq
    (fun i => measurableSet_successEvent R hR root duration target i)
    (successEvents_independent R hR root hroot duration target μ)
    (ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
      (α := α) μ (successSet R duration target))
  · intro i
    exact measure_successEvent R hR root duration target i μ

/-- The first `k` trials all fail with probability `(1-p)^k`. -/
theorem measure_failures_before
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root) (hroot : Function.Injective root)
    (duration target : ℕ) (μ : Measure (Step α X))
    [IsProbabilityMeasure μ] (k : ℕ) :
    RootIndexed.stepFieldLaw (Root := Root) μ
        (⋂ i ∈ Finset.range k, failureEvent R root duration target i) =
      (1 - ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
        (α := α) μ (successSet R duration target)) ^ k := by
  simpa using measure_iInter_failureEvent R hR root hroot
    duration target μ (Finset.range k)

/-- With all natural-number trials enabled, an ordered population declaration
at global generation `n` is precisely the completion at `n` of the first
successful fixed-age trial. -/
theorem mem_orderedPopulationDeclaration_univ_iff
    {Root α X : Type*}
    (R : Step.FiniteSelection α X) (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (threshold duration target n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    ω ∈ orderedCandidateDeclarationWithin
        (completion R root initial threshold duration)
        (fun i => successAtCompletion
          (completion R root initial threshold duration i)
          (successTest R root initial threshold target i))
        Set.univ (fun j i => j < i) n ↔
      ∃ i,
        completion R root initial threshold duration i ω = n ∧
        firstSuccess R root duration target ω = i := by
  rw [mem_orderedPopulationDeclaration_iff R root initial threshold
    duration target Set.univ n ω]
  simp only [Set.mem_univ, true_and]
  constructor
  · rintro ⟨i, hcompletion, hsuccess, hearlier⟩
    exact ⟨i, hcompletion,
      (firstSuccess_eq_iff R root duration target i ω).mpr
        ⟨hsuccess, fun j hj => hearlier j trivial hj⟩⟩
  · rintro ⟨i, hcompletion, hfirst⟩
    obtain ⟨hsuccess, hearlier⟩ :=
      (firstSuccess_eq_iff R root duration target i ω).mp hfirst
    exact ⟨i, hcompletion, hsuccess, fun j _ hj => hearlier j hj⟩

end SplitSchedule
end StepSelection
end RootIndexed
end ProbabilityTheory.BranchingRandomWalk

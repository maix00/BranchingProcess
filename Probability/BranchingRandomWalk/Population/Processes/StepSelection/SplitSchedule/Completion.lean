import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Basic
import Probability.BranchingRandomWalk.Timing.OrderedCandidates

/-!
# Successful completions on a split schedule

Each trial runs for a fixed duration after its observable split-schedule start.
The first ordered success is a stopping time and its generation event has the
usual current-success/earlier-failure form.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed
namespace StepSelection
namespace SplitSchedule

open Combinatorics.UlamHarris Combinatorics.Branching

/-- Fixed-duration completion time of a split-scheduled trial. -/
noncomputable def completion
    {Root α X : Type*}
    (R : Step.FiniteSelection α X) (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (threshold duration i : ℕ)
    (ω : RootIndexed.StepField Root α X) : WithTop ℕ :=
  time R root initial threshold i ω + duration

theorem completion_isStoppingTime
    {Root α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X)
    (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (threshold duration i : ℕ)
    (htime : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (time R root initial threshold i)) :
    IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (completion R root initial threshold duration i) :=
  htime.add_const' duration

theorem completion_isStoppingTime_of_countable
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (hinitial : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) initial)
    (threshold duration i : ℕ) :
    IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (completion R root initial threshold duration i) :=
  completion_isStoppingTime R root initial threshold duration i
    (time_isStoppingTime_of_countable R hR root initial hinitial threshold i)

theorem completion_mono
    {Root α X : Type*}
    (R : Step.FiniteSelection α X) (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (threshold duration : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    Monotone fun i => completion R root initial threshold duration i ω := by
  intro i j hij
  simpa [completion] using add_le_add_left
    (time_mono R root initial threshold ω hij) (duration : WithTop ℕ)

/-- The first successful completed split-scheduled trial is a stopping time. -/
theorem firstSuccessfulCompletion_isStoppingTime
    {Root α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X)
    (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (threshold duration : ℕ)
    (hcompletion : ∀ i, IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (completion R root initial threshold duration i))
    (test : ℕ → ℕ → Set (RootIndexed.StepField Root α X))
    (htest : ∀ i n, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] (test i n))
    (candidates : Set ℕ) :
    IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (firstDeclaredSuccess
        (orderedCandidateDeclarationWithin
          (completion R root initial threshold duration)
          (fun i => successAtCompletion
            (completion R root initial threshold duration i) (test i))
          candidates (fun j i => j < i))) := by
  let F := RootIndexed.stepFiltration
    (Root := Root) (α := α) (X := X)
  have hobservable := successAtCompletion_observable F
    (completion R root initial threshold duration) test hcompletion htest
  exact firstOrderedCandidateCompletionWithin_isStoppingTime F
    (completion R root initial threshold duration)
    (fun i => successAtCompletion
      (completion R root initial threshold duration i) (test i))
    hobservable candidates
      (Set.Countable.mono (Set.subset_univ candidates) Set.countable_univ) _

theorem firstSuccessfulCompletion_isStoppingTime_of_countable
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (hinitial : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) initial)
    (threshold duration : ℕ)
    (test : ℕ → ℕ → Set (RootIndexed.StepField Root α X))
    (htest : ∀ i n, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] (test i n))
    (candidates : Set ℕ) :
    IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (firstDeclaredSuccess
        (orderedCandidateDeclarationWithin
          (completion R root initial threshold duration)
          (fun i => successAtCompletion
            (completion R root initial threshold duration i) (test i))
          candidates (fun j i => j < i))) := by
  apply firstSuccessfulCompletion_isStoppingTime R root initial
    threshold duration
  · exact completion_isStoppingTime_of_countable R hR root initial hinitial
      threshold duration
  · exact htest

theorem mem_orderedDeclaration_iff
    {Root α X : Type*}
    (R : Step.FiniteSelection α X) (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (threshold duration : ℕ)
    (success : ℕ → Set (RootIndexed.StepField Root α X))
    (candidates : Set ℕ) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    ω ∈ orderedCandidateDeclarationWithin
        (completion R root initial threshold duration) success candidates
        (fun j i => j < i) n ↔
      ∃ i ∈ candidates,
        completion R root initial threshold duration i ω = n ∧
          ω ∈ success i ∧
          ∀ j ∈ candidates, j < i → ω ∉ success j := by
  apply mem_orderedCandidateDeclarationWithin_iff
  intro ω' i j _ _ hji
  exact completion_mono R root initial threshold duration ω'
    (Nat.le_of_lt hji)

end SplitSchedule
end StepSelection
end RootIndexed
end ProbabilityTheory.BranchingRandomWalk

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Timing.CausalSchedule
public import Probability.BranchingRandomWalk.Timing.OrderedCandidates

/-!
# Completed trials on a causal schedule

A fixed-duration trial completes a deterministic number of generations after
its causally scheduled start.  The completion times remain stopping times and
are monotone in the pre-sampled trial index.  Therefore the first successful
completed trial is a stopping time and satisfies the usual ordered-failure
formula.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk
namespace CausalSchedule

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Completion of trial `i` a fixed number of generations after its start. -/
noncomputable def completion
    (initial : Ω → WithTop ℕ) (ready : ℕ → ℕ → Set Ω)
    (duration i : ℕ) (ω : Ω) : WithTop ℕ :=
  time initial ready i ω + duration

theorem completion_isStoppingTime
    (F : Filtration ℕ m)
    (initial : Ω → WithTop ℕ) (hinitial : IsStoppingTime F initial)
    (ready : ℕ → ℕ → Set Ω)
    (hready : ∀ i n, MeasurableSet[F n] (ready i n))
    (duration i : ℕ) :
    IsStoppingTime F (completion initial ready duration i) :=
  (time_isStoppingTime F initial hinitial ready hready i).add_const' duration

theorem completion_mono
    (initial : Ω → WithTop ℕ) (ready : ℕ → ℕ → Set Ω)
    (duration : ℕ) (ω : Ω) :
    Monotone fun i => completion initial ready duration i ω := by
  intro i j hij
  simpa [completion] using add_le_add_left
    (time_mono initial ready (ω := ω) hij) (duration : WithTop ℕ)

/-- The first successful fixed-duration trial in a countable set of
pre-sampled trials is a stopping time. -/
theorem firstSuccessfulCompletion_isStoppingTime
    (F : Filtration ℕ m)
    (initial : Ω → WithTop ℕ) (hinitial : IsStoppingTime F initial)
    (ready : ℕ → ℕ → Set Ω)
    (hready : ∀ i n, MeasurableSet[F n] (ready i n))
    (duration : ℕ) (test : ℕ → ℕ → Set Ω)
    (htest : ∀ i n, MeasurableSet[F n] (test i n))
    (candidates : Set ℕ) :
    IsStoppingTime F
      (firstDeclaredSuccess
        (orderedCandidateDeclarationWithin
          (completion initial ready duration)
          (fun i => successAtCompletion
            (completion initial ready duration i) (test i))
          candidates (fun j i => j < i))) := by
  have hcompletion : ∀ i, IsStoppingTime F
      (completion initial ready duration i) :=
    completion_isStoppingTime F initial hinitial ready hready duration
  have hobservable := successAtCompletion_observable F
    (completion initial ready duration) test hcompletion htest
  exact firstOrderedCandidateCompletionWithin_isStoppingTime F
    (completion initial ready duration)
    (fun i => successAtCompletion
      (completion initial ready duration i) (test i))
    hobservable candidates
      (Set.Countable.mono (Set.subset_univ candidates) Set.countable_univ) _

/-- At a finite generation, an ordered declaration is equivalently a
successful trial whose earlier indexed candidates all failed. -/
theorem mem_orderedDeclaration_iff
    (initial : Ω → WithTop ℕ) (ready : ℕ → ℕ → Set Ω)
    (duration : ℕ) (success : ℕ → Set Ω)
    (candidates : Set ℕ) (n : ℕ) (ω : Ω) :
    ω ∈ orderedCandidateDeclarationWithin
        (completion initial ready duration) success candidates
        (fun j i => j < i) n ↔
      ∃ i ∈ candidates,
        completion initial ready duration i ω = n ∧
          ω ∈ success i ∧
          ∀ j ∈ candidates, j < i → ω ∉ success j := by
  apply mem_orderedCandidateDeclarationWithin_iff
  intro ω' i j _ _ hji
  exact completion_mono initial ready duration ω' (Nat.le_of_lt hji)

end CausalSchedule
end ProbabilityTheory.BranchingRandomWalk

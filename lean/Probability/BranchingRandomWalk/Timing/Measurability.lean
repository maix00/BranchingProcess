module

public import Probability.BranchingRandomWalk.Timing.Stopping
public import Probability.Process.HittingTime.ObservableCandidates
public import Probability.Process.Adapted.Recursion

/-!
# Branching-walk compatibility names for observable candidates

General candidate measurability and adapted recursion are owned by
`Probability.Process.HittingTime.ObservableCandidates` and
`Probability.Process.Adapted.Recursion`.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Compatibility name for `ProbabilityTheory.CandidateObservable`. -/
abbrev CandidateObservable {ι : Type*} (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω) : Prop :=
  ProbabilityTheory.CandidateObservable F completion success

/-- Compatibility name for `ProbabilityTheory.successAtCompletion`. -/
abbrev successAtCompletion (completion : Ω → WithTop ℕ)
    (test : ℕ → Set Ω) : Set Ω :=
  ProbabilityTheory.successAtCompletion completion test

theorem successAtCompletion_observable {ι : Type*} (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ) (test : ι → ℕ → Set Ω)
    (hcompletion : ∀ i, IsStoppingTime F (completion i))
    (htest : ∀ i n, MeasurableSet[F n] (test i n)) :
    CandidateObservable F completion
      (fun i => successAtCompletion (completion i) (test i)) :=
  ProbabilityTheory.successAtCompletion_observable F completion test
    hcompletion htest

theorem candidate_declaration_measurable {ι : Type*} [Countable ι]
    (F : Filtration ℕ m) (completion : ι → Ω → WithTop ℕ)
    (success : ι → Set Ω) (h : CandidateObservable F completion success)
    (n : ℕ) :
    MeasurableSet[F n]
      {ω | ∃ i, completion i ω = n ∧ ω ∈ success i} :=
  ProbabilityTheory.candidate_declaration_measurable F completion success h n

/-- Compatibility name for `ProbabilityTheory.successfulCandidateBy`. -/
abbrev successfulCandidateBy
    (completion : ℕ → Ω → WithTop ℕ) (success : ℕ → Set Ω)
    (K T : ℕ) : Set Ω :=
  ProbabilityTheory.successfulCandidateBy completion success K T

theorem successfulCandidateBy_measurable (F : Filtration ℕ m)
    (completion : ℕ → Ω → WithTop ℕ) (success : ℕ → Set Ω)
    (h : CandidateObservable F completion success) (K T : ℕ) :
    MeasurableSet[F T] (successfulCandidateBy completion success K T) :=
  ProbabilityTheory.successfulCandidateBy_measurable F completion success h K T

theorem successfulCandidateBy_compl_measurable (F : Filtration ℕ m)
    (completion : ℕ → Ω → WithTop ℕ) (success : ℕ → Set Ω)
    (h : CandidateObservable F completion success) (K T : ℕ) :
    MeasurableSet[F T] (successfulCandidateBy completion success K T)ᶜ :=
  ProbabilityTheory.successfulCandidateBy_compl_measurable F completion success h K T

/-- Compatibility name for `ProbabilityTheory.successfulCandidateWithin`. -/
abbrev successfulCandidateWithin {ι : Type*}
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (candidates : Set ι) (T : ℕ) : Set Ω :=
  ProbabilityTheory.successfulCandidateWithin completion success candidates T

theorem successfulCandidateWithin_measurable {ι : Type*} (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (h : CandidateObservable F completion success)
    (candidates : Set ι) (hcandidates : candidates.Countable) (T : ℕ) :
    MeasurableSet[F T]
      (successfulCandidateWithin completion success candidates T) :=
  ProbabilityTheory.successfulCandidateWithin_measurable F completion success h
    candidates hcandidates T

/-- Compatibility name for `ProbabilityTheory.candidateDeclarationWithin`. -/
abbrev candidateDeclarationWithin {ι : Type*}
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (candidates : Set ι) (n : ℕ) : Set Ω :=
  ProbabilityTheory.candidateDeclarationWithin completion success candidates n

theorem candidateDeclarationWithin_measurable {ι : Type*} (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (h : CandidateObservable F completion success)
    (candidates : Set ι) (hcandidates : candidates.Countable) (n : ℕ) :
    MeasurableSet[F n]
      (candidateDeclarationWithin completion success candidates n) :=
  ProbabilityTheory.candidateDeclarationWithin_measurable F completion success h
    candidates hcandidates n

theorem first_candidate_completion_within_isStoppingTime {ι : Type*}
    (F : Filtration ℕ m) (completion : ι → Ω → WithTop ℕ)
    (success : ι → Set Ω) (h : CandidateObservable F completion success)
    (candidates : Set ι) (hcandidates : candidates.Countable) :
    IsStoppingTime F
      (firstDeclaredSuccess
        (candidateDeclarationWithin completion success candidates)) :=
  ProbabilityTheory.first_candidate_completion_within_isStoppingTime F
    completion success h candidates hcandidates

theorem first_successful_candidate_within_isStoppingTime {ι : Type*}
    (F : Filtration ℕ m) (completion : ι → Ω → WithTop ℕ)
    (test : ι → ℕ → Set Ω)
    (hcompletion : ∀ i, IsStoppingTime F (completion i))
    (htest : ∀ i n, MeasurableSet[F n] (test i n))
    (candidates : Set ι) (hcandidates : candidates.Countable) :
    IsStoppingTime F
      (firstDeclaredSuccess
        (candidateDeclarationWithin completion
          (fun i => successAtCompletion (completion i) (test i))
          candidates)) :=
  ProbabilityTheory.first_successful_candidate_within_isStoppingTime F
    completion test hcompletion htest candidates hcandidates

theorem first_candidate_completion_isStoppingTime {ι : Type*} [Countable ι]
    (F : Filtration ℕ m) (completion : ι → Ω → WithTop ℕ)
    (success : ι → Set Ω) (h : CandidateObservable F completion success) :
    IsStoppingTime F
      (firstDeclaredSuccess fun n =>
        {ω | ∃ i, completion i ω = n ∧ ω ∈ success i}) :=
  ProbabilityTheory.first_candidate_completion_isStoppingTime F completion
    success h

theorem first_successful_candidate_isStoppingTime {ι : Type*} [Countable ι]
    (F : Filtration ℕ m) (completion : ι → Ω → WithTop ℕ)
    (test : ι → ℕ → Set Ω)
    (hcompletion : ∀ i, IsStoppingTime F (completion i))
    (htest : ∀ i n, MeasurableSet[F n] (test i n)) :
    IsStoppingTime F
      (firstDeclaredSuccess fun n =>
        {ω | ∃ i, completion i ω = n ∧
          ω ∈ successAtCompletion (completion i) (test i)}) :=
  ProbabilityTheory.first_successful_candidate_isStoppingTime F completion
    test hcompletion htest

theorem causal_recursion_adapted {State M : Type*}
    [MeasurableSpace State] [MeasurableSpace M]
    (F : Filtration ℕ m) (state : ℕ → Ω → State)
    (marks : ℕ → Ω → M) (step : State × M → State)
    (hstep : Measurable step)
    (hzero : Measurable[F 0] (state 0))
    (hmarks : ∀ n, Measurable[F (n + 1)] (marks n))
    (hrec : ∀ n ω, state (n + 1) ω = step (state n ω, marks n ω)) :
    ∀ n, Measurable[F n] (state n) :=
  ProbabilityTheory.causal_recursion_adapted F state marks step hstep hzero hmarks hrec

end ProbabilityTheory.BranchingRandomWalk

end

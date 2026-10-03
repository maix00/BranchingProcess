module

public import Mathlib.Probability.Process.HittingTime
public import Probability.Process.HittingTime.Declarations

/-!
# Branching-walk compatibility names for first-success times

The general declarations and stopping-time results live in
`Probability.Process.HittingTime.Declarations`.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Compatibility specialization of mathlib's adapted hitting-time theorem. -/
theorem first_success_isStoppingTime (F : Filtration ℕ m)
    (observable : ℕ → Ω → ℝ) (threshold : ℝ)
    (hadapted : Adapted F observable) :
    IsStoppingTime F (hittingAfter observable (Set.Ici threshold) 0) :=
  hadapted.isStoppingTime_hittingAfter measurableSet_Ici

/-- Compatibility name for `ProbabilityTheory.firstDeclaredSuccess`. -/
noncomputable abbrev firstDeclaredSuccess
    (success : ℕ → Set Ω) : Ω → WithTop ℕ :=
  ProbabilityTheory.firstDeclaredSuccess success

/-- Compatibility name for
`ProbabilityTheory.firstDeclaredSuccess_le_iff`. -/
theorem firstDeclaredSuccess_le_iff
    (success : ℕ → Set Ω) (ω : Ω) (n : ℕ) :
    firstDeclaredSuccess success ω ≤ n ↔
      ∃ j : ℕ, j ≤ n ∧ ω ∈ success j :=
  ProbabilityTheory.firstDeclaredSuccess_le_iff success ω n

/-- Compatibility name for
`ProbabilityTheory.firstDeclaredSuccess_eq_iff`. -/
theorem firstDeclaredSuccess_eq_iff
    (success : ℕ → Set Ω) (ω : Ω) (k : ℕ) :
    firstDeclaredSuccess success ω = k ↔
      ω ∈ success k ∧ ∀ j < k, ω ∉ success j :=
  ProbabilityTheory.firstDeclaredSuccess_eq_iff success ω k

/-- Compatibility name for
`ProbabilityTheory.firstDeclaredSuccess_isStoppingTime`. -/
theorem firstDeclaredSuccess_isStoppingTime (F : Filtration ℕ m)
    (success : ℕ → Set Ω)
    (hmeasure : ∀ n, MeasurableSet[F n] (success n)) :
    IsStoppingTime F (firstDeclaredSuccess success) :=
  ProbabilityTheory.firstDeclaredSuccess_isStoppingTime F success hmeasure

/-- Compatibility name for
`ProbabilityTheory.firstSuccessAfterStopping_isStoppingTime`. -/
theorem firstSuccessAfterStopping_isStoppingTime (F : Filtration ℕ m)
    (start : Ω → WithTop ℕ) (hstart : IsStoppingTime F start)
    (observable : ℕ → Ω → ℝ) (hadapted : Adapted F observable)
    (threshold : ℝ) :
    IsStoppingTime F
      (firstDeclaredSuccess (fun n =>
        {ω | start ω ≤ n ∧ threshold ≤ observable n ω})) :=
  ProbabilityTheory.firstSuccessAfterStopping_isStoppingTime F start hstart
    observable hadapted threshold

end ProbabilityTheory.BranchingRandomWalk

end

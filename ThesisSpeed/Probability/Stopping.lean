import Mathlib.Probability.Process.HittingTime
import Mathlib.Data.Real.Basic

/-!
# The observable first-success time

This verifies the stopping-time mechanism needed for the thesis's rebooting
construction at the abstract process level. Identifying its particular
`τ = τ_κ + ℓ` with this hitting time still requires a formal model of the
restart state and a proof that the success indicator is adapted.
-/

open MeasureTheory

namespace ThesisSpeed

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The first time an adapted real observable crosses a threshold is a
possibly infinite stopping time. This is mathlib's hitting-time theorem
specialized to the generation-size or success observable. -/
theorem first_success_isStoppingTime (F : Filtration ℕ m)
    (observable : ℕ → Ω → ℝ) (threshold : ℝ)
    (hadapted : Adapted F observable) :
    IsStoppingTime F (hittingAfter observable (Set.Ici threshold) 0) :=
  hittingAfter_isStoppingTime hadapted measurableSet_Ici

/-- A time-indexed success declaration. The model must prove that each
declaration belongs to the information available at that generation. -/
noncomputable def firstDeclaredSuccess (success : ℕ → Set Ω) : Ω → WithTop ℕ := by
  classical
  exact hittingAfter (fun n ω => if ω ∈ success n then (1 : ℝ) else 0) (Set.Ici 1) 0

/-- Once the success declaration is measurable at each generation, its first
declaration time is a stopping time. No monotonicity of trial times is needed. -/
theorem firstDeclaredSuccess_isStoppingTime (F : Filtration ℕ m)
    (success : ℕ → Set Ω)
    (hmeasure : ∀ n, MeasurableSet[F n] (success n)) :
    IsStoppingTime F (firstDeclaredSuccess success) := by
  classical
  unfold firstDeclaredSuccess
  apply first_success_isStoppingTime F _ 1
  intro n
  exact ((measurable_const).ite (hmeasure n) measurable_const).stronglyMeasurable

end ThesisSpeed

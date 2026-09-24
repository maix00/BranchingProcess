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

/-- The finite-time event is exactly the union of declarations seen so far. -/
theorem firstDeclaredSuccess_le_iff (success : ℕ → Set Ω) (ω : Ω) (n : ℕ) :
    firstDeclaredSuccess success ω ≤ n ↔
      ∃ j : ℕ, j ≤ n ∧ ω ∈ success j := by
  classical
  unfold firstDeclaredSuccess
  convert (hittingAfter_le_iff (u := fun k x => if x ∈ success k then (1 : ℝ) else 0)
    (s := Set.Ici 1) (n := 0) (i := n) (ω := ω)) using 1
  simp only [Set.mem_Icc, zero_le, true_and, Set.mem_Ici]
  constructor
  · rintro ⟨j, hj, hs⟩
    exact ⟨j, hj, by simp [hs]⟩
  · rintro ⟨j, hj, h⟩
    have hs : ω ∈ success j := by
      by_contra hn
      simp [hn] at h
      norm_num at h
    exact ⟨j, hj, hs⟩

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

/-- A declaration made after a random stopping time is still a stopping time
when its current-generation observable is adapted. This is the abstract
recursion step for an unconditionally pre-defined reserve lineage. -/
theorem firstSuccessAfterStopping_isStoppingTime (F : Filtration ℕ m)
    (start : Ω → WithTop ℕ) (hstart : IsStoppingTime F start)
    (observable : ℕ → Ω → ℝ) (hadapted : Adapted F observable)
    (threshold : ℝ) :
    IsStoppingTime F
      (firstDeclaredSuccess (fun n =>
        {ω | start ω ≤ n ∧ threshold ≤ observable n ω})) := by
  apply firstDeclaredSuccess_isStoppingTime F
  intro n
  exact (hstart n).inter ((hadapted n).measurable measurableSet_Ici)

end ThesisSpeed

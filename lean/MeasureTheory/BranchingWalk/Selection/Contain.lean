import MeasureTheory.BranchingWalk.Step.Field

/-!
# Selection containment on branching walks

`SelectContain ω ω'` says that `ω` is a selection of `ω'`: every present child
of `ω` is present with the same displacement in `ω'`. A selection mechanism is
exactly a map that preserves this order: selecting children can only remove
them, never change or add one. It is a partial order on `BranchingWalk`.
-/

namespace MeasureTheory

namespace BranchingWalk

/-- `ω` is a selection of `ω'`: every present child of `ω` is present with the
same displacement in `ω'`. -/
def SelectContain {α X : Type*} (ω ω' : BranchingWalk α X) : Prop :=
  ∀ u i, present (ω u) i → ω u i = ω' u i

namespace SelectContain

variable {α X : Type*}

@[refl] theorem refl (ω : BranchingWalk α X) : SelectContain ω ω :=
  fun _ _ _ => rfl

@[trans] theorem trans {ω₁ ω₂ ω₃ : BranchingWalk α X}
    (h₁ : SelectContain ω₁ ω₂) (h₂ : SelectContain ω₂ ω₃) :
    SelectContain ω₁ ω₃ := by
  intro u i hp
  rcases hp with ⟨x, hx⟩
  have h₁u : ω₁ u i = ω₂ u i := h₁ u i ⟨x, hx⟩
  have hx₂ : ω₂ u i = some x := by
    rw [h₁u] at hx
    exact hx
  have h₂u : ω₂ u i = ω₃ u i := h₂ u i ⟨x, hx₂⟩
  exact h₁u.trans h₂u

theorem antisymm {ω ω' : BranchingWalk α X}
    (h : SelectContain ω ω') (h' : SelectContain ω' ω) : ω = ω' := by
  funext u i
  by_cases hp : present (ω u) i
  · exact h u i hp
  · have hωnone : ω u i = none := by
      cases hω : ω u i with
      | none => rfl
      | some x => exact (hp ⟨x, hω⟩).elim
    have hnp : ¬ present (ω' u) i := by
      intro hq
      rcases hq with ⟨y, hy⟩
      have hrev : ω' u i = ω u i := h' u i ⟨y, hy⟩
      have hpresent : ω u i = some y := by rw [hrev] at hy; exact hy
      exact hp ⟨y, hpresent⟩
    have hω'none : ω' u i = none := by
      cases hω' : ω' u i with
      | none => rfl
      | some y => exact (hnp ⟨y, hω'⟩).elim
    rw [hωnone, hω'none]

end SelectContain

end BranchingWalk

end MeasureTheory

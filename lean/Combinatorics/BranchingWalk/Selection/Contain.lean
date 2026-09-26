import Combinatorics.BranchingWalk.Basic.Definitions

/-!
# Selection containment on branching walks

`SelectContain β β'` says that `β` is a selection of `β'`: its initial
population is contained in that of `β'`, and every survive child of `β` is
survive with the same displacement in `β'`. It is the partial order that a
selection mechanism preserves: selecting can only remove particles or
children, never change or add one.

`IsParentClosed` is not inherited by an arbitrary subset, so a selection
mechanism that keeps an initial segment declares it explicitly in
`Selection/Mechanism.lean`. Slot order is handled by a separate ordered-step
structure after any reindexing.
-/

namespace Combinatorics

namespace Branching

/-- `β` is a selection of `β'`: its initial population is contained, and every
survive child of `β` is survive with the same displacement in `β'`. -/
def SelectContain {α X : Type*} (β β' : BranchingWalk α X) : Prop :=
  β.initial () ⊆ β'.initial () ∧
    ∀ u i, survive (β.step () u) i → β.step () u i = β'.step () u i

namespace SelectContain

variable {α X : Type*}

@[refl] theorem refl (β : BranchingWalk α X) : SelectContain β β :=
  ⟨fun _ h => h, fun _ _ _ => rfl⟩

@[trans] theorem trans {β₁ β₂ β₃ : BranchingWalk α X}
    (h₁ : SelectContain β₁ β₂) (h₂ : SelectContain β₂ β₃) :
    SelectContain β₁ β₃ := by
  obtain ⟨hi₁, hs₁⟩ := h₁
  obtain ⟨hi₂, hs₂⟩ := h₂
  refine ⟨fun x hx => hi₂ (hi₁ hx), ?_⟩
  intro u i hp
  rcases hp with ⟨x, hx⟩
  have hs₁u : β₁.step () u i = β₂.step () u i := hs₁ u i ⟨x, hx⟩
  have hx₂ : β₂.step () u i = some x := by rw [hs₁u] at hx; exact hx
  have hs₂u : β₂.step () u i = β₃.step () u i := hs₂ u i ⟨x, hx₂⟩
  exact hs₁u.trans hs₂u

theorem antisymm {β β' : BranchingWalk α X}
    (h : SelectContain β β') (h' : SelectContain β' β) : β = β' := by
  obtain ⟨hi, hs⟩ := h
  obtain ⟨hi', hs'⟩ := h'
  apply RootIndexed.BranchingWalk.ext
  · funext r
    cases r
    funext u i
    by_cases hp : survive (β.step () u) i
    · exact hs u i hp
    · have hωnone : β.step () u i = none := by
        cases hω : β.step () u i with
        | none => rfl
        | some x => exact (hp ⟨x, hω⟩).elim
      have hnp : ¬ survive (β'.step () u) i := by
        intro hq
        rcases hq with ⟨y, hy⟩
        have hrev : β'.step () u i = β.step () u i := hs' u i ⟨y, hy⟩
        have hsurvive : β.step () u i = some y := by rw [hrev] at hy; exact hy
        exact hp ⟨y, hsurvive⟩
      have hω'none : β'.step () u i = none := by
        cases hω' : β'.step () u i with
        | none => rfl
        | some y => exact (hnp ⟨y, hω'⟩).elim
      rw [hωnone, hω'none]
  · funext r
    cases r
    exact Set.Subset.antisymm hi hi'

end SelectContain

end Branching

end Combinatorics

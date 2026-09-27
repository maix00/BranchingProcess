import Combinatorics.BranchingWalk.Basic.Definitions

/-!
# Selection containment on branching walks

`RootIndexed.SelectContain β β'` says that `β` is a selection of `β'`: its initial
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

namespace RootIndexed

/-- `β` is a selection of `β'`: every root keeps its initial position, and every
selected child survives with the same displacement in the source walk. -/
def SelectContain {Root α Mark Position : Type*}
    (β β' : RootIndexed.BranchingWalk Root α Mark Position) : Prop :=
  (∀ r, β.initial r = β'.initial r) ∧
    ∀ r u i, survive (β.step r u) i → β.step r u i = β'.step r u i

namespace SelectContain

variable {Root α Mark Position : Type*}

@[refl] theorem refl
    (β : RootIndexed.BranchingWalk Root α Mark Position) : SelectContain β β :=
  ⟨fun _ => rfl, fun _ _ _ _ => rfl⟩

@[trans] theorem trans
    {β₁ β₂ β₃ : RootIndexed.BranchingWalk Root α Mark Position}
    (h₁ : SelectContain β₁ β₂) (h₂ : SelectContain β₂ β₃) :
    SelectContain β₁ β₃ := by
  obtain ⟨hi₁, hs₁⟩ := h₁
  obtain ⟨hi₂, hs₂⟩ := h₂
  refine ⟨fun r => (hi₁ r).trans (hi₂ r), ?_⟩
  intro r u i hp
  rcases hp with ⟨x, hx⟩
  have hs₁u : β₁.step r u i = β₂.step r u i := hs₁ r u i ⟨x, hx⟩
  have hx₂ : β₂.step r u i = some x := by rw [hs₁u] at hx; exact hx
  have hs₂u : β₂.step r u i = β₃.step r u i := hs₂ r u i ⟨x, hx₂⟩
  exact hs₁u.trans hs₂u

theorem antisymm {β β' : RootIndexed.BranchingWalk Root α Mark Position}
    (h : SelectContain β β') (h' : SelectContain β' β) : β = β' := by
  obtain ⟨hi, hs⟩ := h
  obtain ⟨hi', hs'⟩ := h'
  apply RootIndexed.BranchingWalk.ext
  · funext r
    funext u i
    by_cases hp : survive (β.step r u) i
    · exact hs r u i hp
    · have hωnone : β.step r u i = none := by
        cases hω : β.step r u i with
        | none => rfl
        | some x => exact (hp ⟨x, hω⟩).elim
      have hnp : ¬ survive (β'.step r u) i := by
        intro hq
        rcases hq with ⟨y, hy⟩
        have hrev : β'.step r u i = β.step r u i := hs' r u i ⟨y, hy⟩
        have hsurvive : β.step r u i = some y := by rw [hrev] at hy; exact hy
        exact hp ⟨y, hsurvive⟩
      have hω'none : β'.step r u i = none := by
        cases hω' : β'.step r u i with
        | none => rfl
        | some y => exact (hnp ⟨y, hω'⟩).elim
      rw [hωnone, hω'none]
  · funext r
    exact hi r

end SelectContain

end RootIndexed

/-- Single-root selection containment, definitionally the `PUnit` instance of
root-indexed containment. -/
abbrev SelectContain {α Mark Position : Type*}
    (β β' : BranchingWalk α Mark Position) : Prop :=
  RootIndexed.SelectContain β β'

end Branching

end Combinatorics

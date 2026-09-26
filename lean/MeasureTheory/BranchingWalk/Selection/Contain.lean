import MeasureTheory.BranchingWalk.Basic
import MeasureTheory.BranchingWalk.Relation.Field

/-!
# Selection containment on branching walks

`SelectContain β β'` says that `β` is a selection of `β'`: its initial
population is contained in that of `β'`, and every present child of `β` is
present with the same displacement in `β'`. It is the partial order that a
selection mechanism preserves: selecting can only remove particles or
children, never change or add one.

`IsOrdered` is inherited automatically by containment: a sub-walk of an ordered
walk is ordered. `IsParentClosed` is not inherited by an arbitrary subset, so a
selection mechanism that keeps an initial segment declares it explicitly in
`Selection/Mechanism.lean`.
-/

namespace MeasureTheory

namespace BranchingWalk

/-- `β` is a selection of `β'`: its initial population is contained, and every
present child of `β` is present with the same displacement in `β'`. -/
def SelectContain {α X : Type*} (β β' : BranchingWalk α X) : Prop :=
  β.initial () ⊆ β'.initial () ∧
    ∀ u i, present (β.step () u) i → β.step () u i = β'.step () u i

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
  apply RootIndexedBranchingWalk.ext
  · funext r
    cases r
    funext u i
    by_cases hp : present (β.step () u) i
    · exact hs u i hp
    · have hωnone : β.step () u i = none := by
        cases hω : β.step () u i with
        | none => rfl
        | some x => exact (hp ⟨x, hω⟩).elim
      have hnp : ¬ present (β'.step () u) i := by
        intro hq
        rcases hq with ⟨y, hy⟩
        have hrev : β'.step () u i = β.step () u i := hs' u i ⟨y, hy⟩
        have hpresent : β.step () u i = some y := by rw [hrev] at hy; exact hy
        exact hp ⟨y, hpresent⟩
      have hω'none : β'.step () u i = none := by
        cases hω' : β'.step () u i with
        | none => rfl
        | some y => exact (hnp ⟨y, hω'⟩).elim
      rw [hωnone, hω'none]
  · funext r
    cases r
    exact Set.Subset.antisymm hi hi'

/-- Containment inherits the mark order: a sub-walk of an ordered walk is
ordered. -/
theorem isOrdered_of_selectContain {α X : Type*} [LT α] [LE X]
    {β β' : BranchingWalk α X}
    (h : SelectContain β β') (ho : IsOrdered (β'.step ())) : IsOrdered (β.step ()) := by
  intro u
  unfold markOrdered
  intro i j x y hij hx hy
  have hx' : β'.step () u i = some x := (h.2 u i ⟨x, hx⟩).symm.trans hx
  have hy' : β'.step () u j = some y := (h.2 u j ⟨y, hy⟩).symm.trans hy
  exact ho u i j x y hij hx' hy'

end SelectContain

end BranchingWalk

end MeasureTheory

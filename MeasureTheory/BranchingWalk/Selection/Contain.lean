import MeasureTheory.BranchingWalk.Basic
import MeasureTheory.BranchingWalk.Step.Ordered.Field
import MeasureTheory.BranchingWalk.Relation.Field

/-!
# Selection containment on branching walks

`SelectContain ω ω'` says that `ω` is a selection of `ω'`: its initial
population is contained in that of `ω'`, and every present child of `ω` is
present with the same displacement in `ω'`. It is the partial order that a
selection mechanism preserves: selecting can only remove particles or
children, never change or add one.

`IsOrdered` is inherited automatically by containment: a sub-walk of an ordered
walk is ordered. `IsParentClosed` is not inherited by an arbitrary subset, so a
selection mechanism that keeps an initial segment declares it explicitly in
`Selection/Mechanism.lean`.
-/

namespace MeasureTheory

namespace BranchingWalk

/-- `ω` is a selection of `ω'`: its initial population is contained, and every
present child of `ω` is present with the same displacement in `ω'`. -/
def SelectContain {α X : Type*} (ω ω' : BranchingWalk α X) : Prop :=
  ω.initial () ⊆ ω'.initial () ∧
    ∀ u i, present (ω.step () u) i → ω.step () u i = ω'.step () u i

namespace SelectContain

variable {α X : Type*}

@[refl] theorem refl (ω : BranchingWalk α X) : SelectContain ω ω :=
  ⟨fun _ h => h, fun _ _ _ => rfl⟩

@[trans] theorem trans {ω₁ ω₂ ω₃ : BranchingWalk α X}
    (h₁ : SelectContain ω₁ ω₂) (h₂ : SelectContain ω₂ ω₃) :
    SelectContain ω₁ ω₃ := by
  obtain ⟨hi₁, hs₁⟩ := h₁
  obtain ⟨hi₂, hs₂⟩ := h₂
  refine ⟨fun x hx => hi₂ (hi₁ hx), ?_⟩
  intro u i hp
  rcases hp with ⟨x, hx⟩
  have hs₁u : ω₁.step () u i = ω₂.step () u i := hs₁ u i ⟨x, hx⟩
  have hx₂ : ω₂.step () u i = some x := by rw [hs₁u] at hx; exact hx
  have hs₂u : ω₂.step () u i = ω₃.step () u i := hs₂ u i ⟨x, hx₂⟩
  exact hs₁u.trans hs₂u

theorem antisymm {ω ω' : BranchingWalk α X}
    (h : SelectContain ω ω') (h' : SelectContain ω' ω) : ω = ω' := by
  obtain ⟨hi, hs⟩ := h
  obtain ⟨hi', hs'⟩ := h'
  apply RootIndexedBranchingWalk.ext
  · funext r
    cases r
    funext u i
    by_cases hp : present (ω.step () u) i
    · exact hs u i hp
    · have hωnone : ω.step () u i = none := by
        cases hω : ω.step () u i with
        | none => rfl
        | some x => exact (hp ⟨x, hω⟩).elim
      have hnp : ¬ present (ω'.step () u) i := by
        intro hq
        rcases hq with ⟨y, hy⟩
        have hrev : ω'.step () u i = ω.step () u i := hs' u i ⟨y, hy⟩
        have hpresent : ω.step () u i = some y := by rw [hrev] at hy; exact hy
        exact hp ⟨y, hpresent⟩
      have hω'none : ω'.step () u i = none := by
        cases hω' : ω'.step () u i with
        | none => rfl
        | some y => exact (hnp ⟨y, hω'⟩).elim
      rw [hωnone, hω'none]
  · funext r
    cases r
    exact Set.Subset.antisymm hi hi'

/-- Containment inherits the mark order: a sub-walk of an ordered walk is
ordered. -/
theorem isOrdered_of_selectContain {α X : Type*} [LT α] [LE X]
    {ω ω' : BranchingWalk α X}
    (h : SelectContain ω ω') (ho : IsOrdered (ω'.step ())) : IsOrdered (ω.step ()) := by
  intro u
  unfold parentOrdered
  intro i j x y hij hx hy
  have hx' : ω'.step () u i = some x := (h.2 u i ⟨x, hx⟩).symm.trans hx
  have hy' : ω'.step () u j = some y := (h.2 u j ⟨y, hy⟩).symm.trans hy
  exact ho u i j x y hij hx' hy'

end SelectContain

end BranchingWalk

end MeasureTheory

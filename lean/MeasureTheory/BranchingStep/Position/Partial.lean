import MeasureTheory.BranchingStep.Position.Accumulate
import MeasureTheory.BranchingStep.Position.Increment
import MeasureTheory.BranchingStep.Tree.Realization

/-!
# The partial accumulated mark

`accumulate?` is the same path recursion as
`accumulate`, but it accumulates in `Option X`: as soon
as one slot on the path is absent it returns `none`. Being a direct recursion,
it needs neither `classical` nor a decision procedure for
`realizedNode`. The main lemma binds the three readings — the partial
mark has a value, the path is realized, and that value is the total mark — and
the paper's prefix sums are kept as bridge lemmas in both indexings.
-/

namespace MeasureTheory

namespace BranchingStep

open MeasureTheory.UlamHarris



/-- The partial accumulated mark along the remaining path `p` from the address
`v`; `none` as soon as one slot on the path is absent. -/
def accumulate? {α X : Type*} [AddCommMonoid X]
    (ω : StepField α X) : TreeNode α → TreeNode α → Option X
  | _, [] => some 0
  | v, i :: p =>
      (ω v i).bind fun x =>
        (accumulate? ω (v ++ [i]) p).map fun y => x + y

/-- Accumulated mark from the root to `u`; `none` when a slot on the root path
is absent. -/
def accumulateRoot? {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) (u : TreeNode α) : Option X :=
  accumulate? step [] u

@[simp] theorem accumulate?_nil {α X : Type*} [AddCommMonoid X]
    (ω : StepField α X) (v : TreeNode α) :
    accumulate? ω v [] = some 0 := rfl

theorem accumulate?_cons {α X : Type*} [AddCommMonoid X]
    (ω : StepField α X) (v : TreeNode α) (i : α) (p : TreeNode α) :
    accumulate? ω v (i :: p) =
      (ω v i).bind fun x =>
        (accumulate? ω (v ++ [i]) p).map fun y => x + y := rfl

theorem accumulate?_eq_none_iff {α X : Type*} [AddCommMonoid X]
    (ω : StepField α X) (v p : TreeNode α) :
    accumulate? ω v p = none ↔
      ¬ presentAlong ω v p := by
  induction p generalizing v with
  | nil => simp [presentAlong]
  | cons i p ih =>
      rw [accumulate?_cons, presentAlong_cons]
      cases h : ω v i with
      | none => simp [h, present]
      | some x =>
          have hp : present (ω v) i := ⟨x, h⟩
          simp [hp, ih (v := v ++ [i]), Option.map_eq_none_iff]

/-- On a realized path the partial recursion returns the total accumulated
mark. -/
theorem accumulate?_eq_some_of_present {α X : Type*}
    [AddCommMonoid X] (ω : StepField α X) :
    ∀ (v p : TreeNode α), presentAlong ω v p →
      accumulate? ω v p =
        some (accumulate ω v p)
  | v, [], _ => rfl
  | v, i :: p, h => by
      obtain ⟨x, hx⟩ := h.1
      have ih := accumulate?_eq_some_of_present ω (v ++ [i]) p h.2
      rw [accumulate?_cons, accumulate_cons,
        value_some (ω v) i x hx, hx, ih]
      simp

/-- The three readings of the partial mark — it has a value, the path is
realized, and that value is the total accumulated mark — are one statement. -/
theorem accumulate?_eq_some_iff {α X : Type*} [AddCommMonoid X]
    (ω : StepField α X) (v p : TreeNode α) (x : X) :
    accumulate? ω v p = some x ↔
      presentAlong ω v p ∧
        accumulate ω v p = x := by
  constructor
  · intro h
    by_cases hp : presentAlong ω v p
    · have htot := accumulate?_eq_some_of_present ω v p hp
      rw [htot] at h
      exact ⟨hp, Option.some.inj h⟩
    · have hnone := (accumulate?_eq_none_iff ω v p).mpr hp
      rw [hnone] at h
      exact absurd h (by simp)
  · rintro ⟨hp, rfl⟩
    exact accumulate?_eq_some_of_present ω v p hp

theorem accumulate?_isSome_iff {α X : Type*} [AddCommMonoid X]
    (ω : StepField α X) (v p : TreeNode α) :
    (accumulate? ω v p).isSome ↔
      presentAlong ω v p := by
  cases h : accumulate? ω v p with
  | none => simp [(accumulate?_eq_none_iff ω v p).mp h]
  | some x =>
      have hp : presentAlong ω v p :=
        ((accumulate?_eq_some_iff ω v p x).mp h).1
      simp [hp]

@[simp] theorem accumulateRoot?_nil {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) : accumulateRoot? step [] = some 0 := rfl

theorem accumulateRoot?_eq_some_iff {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) (u : TreeNode α) (x : X) :
    accumulateRoot? step u = some x ↔
      realizedNode step u ∧ accumulateRoot step u = x := by
  simpa [accumulateRoot?, realizedNode, accumulateRoot]
    using accumulate?_eq_some_iff step [] u x

theorem accumulateRoot?_eq_some_of_realized {α X : Type*}
    [AddCommMonoid X] (step : StepField α X) {u : TreeNode α}
    (h : realizedNode step u) :
    accumulateRoot? step u = some (accumulateRoot step u) :=
  (accumulateRoot?_eq_some_iff step u _).mpr ⟨h, rfl⟩

theorem accumulateRoot?_eq_none_iff {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) (u : TreeNode α) :
    accumulateRoot? step u = none ↔ ¬ realizedNode step u := by
  simpa [accumulateRoot?, realizedNode] using
    accumulate?_eq_none_iff step [] u

theorem accumulateRoot?_isSome_iff {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) (u : TreeNode α) :
    (accumulateRoot? step u).isSome ↔ realizedNode step u := by
  simpa [accumulateRoot?, realizedNode] using
    accumulate?_isSome_iff step [] u

/-- The partial mark in the paper's range-indexed sum form: it is `some x`
exactly when the address is realized and the accumulated increment equals `x`.
The `getD 0` guard absorbs the indices outside the range; realizability is
carried separately by the first conjunct. -/
theorem accumulateRoot?_eq_some_sum_iff {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) (u : TreeNode α) (x : X) :
    accumulateRoot? step u = some x ↔
      realizedNode step u ∧
        (∑ j ∈ Finset.range u.length,
          (Option.map (MeasureTheory.BranchingStep.value (step (u.take j))) (u[j]?)).getD 0) = x := by
  rw [accumulateRoot?_eq_some_iff, accumulateRoot_eq_sum]

/-- The partial mark in the `Fin`-indexed sum form. -/
theorem accumulateRoot?_eq_some_sum_fin_iff {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) (u : TreeNode α) (x : X) :
    accumulateRoot? step u = some x ↔
      (∀ j : Fin u.length, present (step (u.take j)) (u[j])) ∧
        (∑ j : Fin u.length, MeasureTheory.BranchingStep.value (step (u.take j)) (u[j])) = x := by
  rw [accumulateRoot?_eq_some_iff, realizedNode_iff_forall_fin,
    accumulateRoot_eq_sum_fin]

/-- Appending one step: the partial mark at `u ++ [i]` is `some` of the
incremented total exactly when `u` is realized and the slot at `i` is present.
This replaces the earlier statement that wrapped the total definition in an
`if`, which forced a `Classical.propDecidable` instance into the conclusion. -/
theorem accumulateRoot?_append_singleton
    {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) (u : TreeNode α) (i : α) :
    accumulateRoot? step (u ++ [i]) =
        some (accumulateRoot step u + MeasureTheory.BranchingStep.value (step u) i) ↔
      realizedNode step u ∧ present (step u) i := by
  rw [accumulateRoot?_eq_some_iff, realizedNode_append_singleton_iff,
    accumulateRoot_append_singleton]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

end BranchingStep

end MeasureTheory

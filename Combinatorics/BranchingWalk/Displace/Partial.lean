import Combinatorics.BranchingWalk.Displace.Basic
import Combinatorics.BranchingWalk.Step.Basic
import Combinatorics.BranchingWalk.Basic.SurviveAlong

/-!
# The partial displacement

`displace?` is the same path recursion as
`displace`, but it computes in `Option X`: as soon
as one slot on the path is absent it returns `none`. Being a direct recursion,
it needs neither `classical` nor a decision procedure for
`surviveAlong step []`. The main lemma binds the three readings — the partial
mark has a value, the path is realized, and that value is the total mark — and
the paper's prefix sums are kept as bridge lemmas in both indexings.
-/

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris



/-- The partial displacement along the remaining path `p` from the address
`v`; `none` as soon as one slot on the path is absent. -/
def displace? {α X : Type*} [AddCommMonoid X]
    (β : StepField α X) : TreeNode α → TreeNode α → Option X
  | _, [] => some 0
  | v, i :: p =>
      (β v i).bind fun x =>
        (displace? β (v ++ [i]) p).map fun y => x + y

/-- Displaced mark from the root to `u`; `none` when a slot on the root path
is absent. -/
def displaceRoot? {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) (u : TreeNode α) : Option X :=
  displace? step [] u

@[simp] theorem displace?_nil {α X : Type*} [AddCommMonoid X]
    (β : StepField α X) (v : TreeNode α) :
    displace? β v [] = some 0 := rfl

theorem displace?_cons {α X : Type*} [AddCommMonoid X]
    (β : StepField α X) (v : TreeNode α) (i : α) (p : TreeNode α) :
    displace? β v (i :: p) =
      (β v i).bind fun x =>
        (displace? β (v ++ [i]) p).map fun y => x + y := rfl

theorem displace?_eq_none_iff {α X : Type*} [AddCommMonoid X]
    (β : StepField α X) (v p : TreeNode α) :
    displace? β v p = none ↔
      ¬ surviveAlong β v p := by
  induction p generalizing v with
  | nil => simp [surviveAlong]
  | cons i p ih =>
      rw [displace?_cons, surviveAlong_cons]
      cases h : β v i with
      | none => simp [h, survive]
      | some x =>
          have hp : survive (β v) i := ⟨x, h⟩
          simp [hp, ih (v := v ++ [i]), Option.map_eq_none_iff]

/-- On a realized path the partial recursion returns the total displacement
mark. -/
theorem displace?_eq_some_of_survive {α X : Type*}
    [AddCommMonoid X] (β : StepField α X) :
    ∀ (v p : TreeNode α), surviveAlong β v p →
      displace? β v p =
        some (displace β v p)
  | v, [], _ => rfl
  | v, i :: p, h => by
      obtain ⟨x, hx⟩ := h.1
      have ih := displace?_eq_some_of_survive β (v ++ [i]) p h.2
      rw [displace?_cons, displace_cons,
        value'_some (β v) i x hx, hx, ih]
      simp

/-- The three readings of the partial mark — it has a value, the path is
realized, and that value is the total displacement — are one statement. -/
theorem displace?_eq_some_iff {α X : Type*} [AddCommMonoid X]
    (β : StepField α X) (v p : TreeNode α) (x : X) :
    displace? β v p = some x ↔
      surviveAlong β v p ∧
        displace β v p = x := by
  constructor
  · intro h
    by_cases hp : surviveAlong β v p
    · have htot := displace?_eq_some_of_survive β v p hp
      rw [htot] at h
      exact ⟨hp, Option.some.inj h⟩
    · have hnone := (displace?_eq_none_iff β v p).mpr hp
      rw [hnone] at h
      exact absurd h (by simp)
  · rintro ⟨hp, rfl⟩
    exact displace?_eq_some_of_survive β v p hp

theorem displace?_isSome_iff {α X : Type*} [AddCommMonoid X]
    (β : StepField α X) (v p : TreeNode α) :
    (displace? β v p).isSome ↔
      surviveAlong β v p := by
  cases h : displace? β v p with
  | none => simp [(displace?_eq_none_iff β v p).mp h]
  | some x =>
      have hp : surviveAlong β v p :=
        ((displace?_eq_some_iff β v p x).mp h).1
      simp [hp]

@[simp] theorem displaceRoot?_nil {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) : displaceRoot? step [] = some 0 := rfl

theorem displaceRoot?_eq_some_iff {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) (u : TreeNode α) (x : X) :
    displaceRoot? step u = some x ↔
      surviveAlong step [] step u ∧ displaceRoot step u = x := by
  simpa [displaceRoot?, surviveAlong step [], displaceRoot]
    using displace?_eq_some_iff step [] u x

theorem displaceRoot?_eq_some_of_realized {α X : Type*}
    [AddCommMonoid X] (step : StepField α X) {u : TreeNode α}
    (h : surviveAlong step [] step u) :
    displaceRoot? step u = some (displaceRoot step u) :=
  (displaceRoot?_eq_some_iff step u _).mpr ⟨h, rfl⟩

theorem displaceRoot?_eq_none_iff {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) (u : TreeNode α) :
    displaceRoot? step u = none ↔ ¬ surviveAlong step [] step u := by
  simpa [displaceRoot?, surviveAlong step []] using
    displace?_eq_none_iff step [] u

theorem displaceRoot?_isSome_iff {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) (u : TreeNode α) :
    (displaceRoot? step u).isSome ↔ surviveAlong step [] step u := by
  simpa [displaceRoot?, surviveAlong step []] using
    displace?_isSome_iff step [] u

/-- The partial mark in the paper's range-indexed sum form: it is `some x`
exactly when the address is realized and the displacement equals `x`.
The `getD 0` guard absorbs the indices outside the range; realizability is
carried separately by the first conjunct. -/
theorem displaceRoot?_eq_some_sum_iff {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) (u : TreeNode α) (x : X) :
    displaceRoot? step u = some x ↔
      surviveAlong step [] step u ∧
        (∑ j ∈ Finset.range u.length,
          (Option.map (Combinatorics.Branching.value' (step (u.take j))) (u[j]?)).getD 0) = x := by
  rw [displaceRoot?_eq_some_iff, displaceRoot_eq_sum]

/-- The partial mark in the `Fin`-indexed sum form. -/
theorem displaceRoot?_eq_some_sum_fin_iff {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) (u : TreeNode α) (x : X) :
    displaceRoot? step u = some x ↔
      (∀ j : Fin u.length, survive (step (u.take j)) (u[j])) ∧
        (∑ j : Fin u.length, Combinatorics.Branching.value' (step (u.take j)) (u[j])) = x := by
  rw [displaceRoot?_eq_some_iff, surviveAlong_root_iff_forall_fin,
    displaceRoot_eq_sum_fin]

/-- Appending one step: the partial mark at `u ++ [i]` is `some` of the
incremented total exactly when `u` is realized and the slot at `i` is survive.
This replaces the earlier statement that wrapped the total definition in an
`if`, which forced a `Classical.propDecidable` instance into the conclusion. -/
theorem displaceRoot?_append_singleton
    {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) (u : TreeNode α) (i : α) :
    displaceRoot? step (u ++ [i]) =
        some (displaceRoot step u + Combinatorics.Branching.value' (step u) i) ↔
      surviveAlong step [] step u ∧ survive (step u) i := by
  rw [displaceRoot?_eq_some_iff, surviveAlong_root_append_singleton_iff,
    displaceRoot_append_singleton]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

end Branching

end Combinatorics

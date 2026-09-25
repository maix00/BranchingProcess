import ThesisSpeed.Probability.Genealogy.BranchingStep.AccumulatedMark
import ThesisSpeed.Probability.Genealogy.BranchingStep.Realization

/-!
# The partial accumulated mark

`branchingStepAccumulatedMarkFrom?` is the same path recursion as
`branchingStepAccumulatedMarkFrom`, but it accumulates in `Option X`: as soon
as one slot on the path is absent it returns `none`. Being a direct recursion,
it needs neither `classical` nor a decision procedure for
`branchingRealizedNode`. The main lemma binds the three readings — the partial
mark has a value, the path is realized, and that value is the total mark — and
the paper's prefix sums are kept as bridge lemmas in both indexings.
-/

namespace ThesisSpeed

/-- The partial accumulated mark along the remaining path `p` from the address
`v`; `none` as soon as one slot on the path is absent. -/
def branchingStepAccumulatedMarkFrom? {α X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) : TreeNode α → TreeNode α → Option X
  | _, [] => some 0
  | v, i :: p =>
      (ω v i).bind fun x =>
        (branchingStepAccumulatedMarkFrom? ω (v ++ [i]) p).map fun y => x + y

/-- Accumulated mark from the root to `u`; `none` when a slot on the root path
is absent. -/
def branchingStepAccumulatedMark? {α X : Type*} [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) : Option X :=
  branchingStepAccumulatedMarkFrom? step [] u

@[simp] theorem branchingStepAccumulatedMarkFrom?_nil {α X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (v : TreeNode α) :
    branchingStepAccumulatedMarkFrom? ω v [] = some 0 := rfl

theorem branchingStepAccumulatedMarkFrom?_cons {α X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (v : TreeNode α) (i : α) (p : TreeNode α) :
    branchingStepAccumulatedMarkFrom? ω v (i :: p) =
      (ω v i).bind fun x =>
        (branchingStepAccumulatedMarkFrom? ω (v ++ [i]) p).map fun y => x + y := rfl

theorem branchingStepAccumulatedMarkFrom?_eq_none_iff {α X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (v p : TreeNode α) :
    branchingStepAccumulatedMarkFrom? ω v p = none ↔
      ¬ branchingStepPresentAlong ω v p := by
  induction p generalizing v with
  | nil => simp [branchingStepPresentAlong]
  | cons i p ih =>
      rw [branchingStepAccumulatedMarkFrom?_cons, branchingStepPresentAlong_cons]
      cases h : ω v i with
      | none => simp [h, branchingStepPresent]
      | some x =>
          have hp : branchingStepPresent (ω v) i := ⟨x, h⟩
          simp [hp, ih (v := v ++ [i]), Option.map_eq_none_iff]

/-- On a realized path the partial recursion returns the total accumulated
mark. -/
theorem branchingStepAccumulatedMarkFrom?_eq_some_of_present {α X : Type*}
    [AddCommMonoid X] (ω : BranchingStepField α X) :
    ∀ (v p : TreeNode α), branchingStepPresentAlong ω v p →
      branchingStepAccumulatedMarkFrom? ω v p =
        some (branchingStepAccumulatedMarkFrom ω v p)
  | v, [], _ => rfl
  | v, i :: p, h => by
      obtain ⟨x, hx⟩ := h.1
      have ih := branchingStepAccumulatedMarkFrom?_eq_some_of_present ω (v ++ [i]) p h.2
      rw [branchingStepAccumulatedMarkFrom?_cons, branchingStepAccumulatedMarkFrom_cons,
        branchingStepIncrement_some (ω v) i x hx, hx, ih]
      simp

/-- The three readings of the partial mark — it has a value, the path is
realized, and that value is the total accumulated mark — are one statement. -/
theorem branchingStepAccumulatedMarkFrom?_eq_some_iff {α X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (v p : TreeNode α) (x : X) :
    branchingStepAccumulatedMarkFrom? ω v p = some x ↔
      branchingStepPresentAlong ω v p ∧
        branchingStepAccumulatedMarkFrom ω v p = x := by
  constructor
  · intro h
    by_cases hp : branchingStepPresentAlong ω v p
    · have htot := branchingStepAccumulatedMarkFrom?_eq_some_of_present ω v p hp
      rw [htot] at h
      exact ⟨hp, Option.some.inj h⟩
    · have hnone := (branchingStepAccumulatedMarkFrom?_eq_none_iff ω v p).mpr hp
      rw [hnone] at h
      exact absurd h (by simp)
  · rintro ⟨hp, rfl⟩
    exact branchingStepAccumulatedMarkFrom?_eq_some_of_present ω v p hp

theorem branchingStepAccumulatedMarkFrom?_isSome_iff {α X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (v p : TreeNode α) :
    (branchingStepAccumulatedMarkFrom? ω v p).isSome ↔
      branchingStepPresentAlong ω v p := by
  cases h : branchingStepAccumulatedMarkFrom? ω v p with
  | none => simp [(branchingStepAccumulatedMarkFrom?_eq_none_iff ω v p).mp h]
  | some x =>
      have hp : branchingStepPresentAlong ω v p :=
        ((branchingStepAccumulatedMarkFrom?_eq_some_iff ω v p x).mp h).1
      simp [hp]

@[simp] theorem branchingStepAccumulatedMark?_nil {α X : Type*} [AddCommMonoid X]
    (step : BranchingStepField α X) : branchingStepAccumulatedMark? step [] = some 0 := rfl

theorem branchingStepAccumulatedMark?_eq_some_iff {α X : Type*} [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) (x : X) :
    branchingStepAccumulatedMark? step u = some x ↔
      branchingRealizedNode step u ∧ branchingStepAccumulatedMark step u = x := by
  simpa [branchingStepAccumulatedMark?, branchingRealizedNode, branchingStepAccumulatedMark]
    using branchingStepAccumulatedMarkFrom?_eq_some_iff step [] u x

theorem branchingStepAccumulatedMark?_eq_some_of_realized {α X : Type*}
    [AddCommMonoid X] (step : BranchingStepField α X) {u : TreeNode α}
    (h : branchingRealizedNode step u) :
    branchingStepAccumulatedMark? step u = some (branchingStepAccumulatedMark step u) :=
  (branchingStepAccumulatedMark?_eq_some_iff step u _).mpr ⟨h, rfl⟩

theorem branchingStepAccumulatedMark?_eq_none_iff {α X : Type*} [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) :
    branchingStepAccumulatedMark? step u = none ↔ ¬ branchingRealizedNode step u := by
  simpa [branchingStepAccumulatedMark?, branchingRealizedNode] using
    branchingStepAccumulatedMarkFrom?_eq_none_iff step [] u

theorem branchingStepAccumulatedMark?_isSome_iff {α X : Type*} [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) :
    (branchingStepAccumulatedMark? step u).isSome ↔ branchingRealizedNode step u := by
  simpa [branchingStepAccumulatedMark?, branchingRealizedNode] using
    branchingStepAccumulatedMarkFrom?_isSome_iff step [] u

/-- The partial mark in the paper's range-indexed sum form: it is `some x`
exactly when the address is realized and the accumulated increment equals `x`.
The `getD 0` guard absorbs the indices outside the range; realizability is
carried separately by the first conjunct. -/
theorem branchingStepAccumulatedMark?_eq_some_sum_iff {α X : Type*} [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) (x : X) :
    branchingStepAccumulatedMark? step u = some x ↔
      branchingRealizedNode step u ∧
        (∑ j ∈ Finset.range u.length,
          (Option.map (branchingStepIncrement (step (u.take j))) (u[j]?)).getD 0) = x := by
  rw [branchingStepAccumulatedMark?_eq_some_iff, branchingStepAccumulatedMark_eq_sum]

/-- The partial mark in the `Fin`-indexed sum form. -/
theorem branchingStepAccumulatedMark?_eq_some_sum_fin_iff {α X : Type*} [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) (x : X) :
    branchingStepAccumulatedMark? step u = some x ↔
      (∀ j : Fin u.length, branchingStepPresent (step (u.take j)) (u[j])) ∧
        (∑ j : Fin u.length, branchingStepIncrement (step (u.take j)) (u[j])) = x := by
  rw [branchingStepAccumulatedMark?_eq_some_iff, branchingRealizedNode_iff_forall_fin,
    branchingStepAccumulatedMark_eq_sum_fin]

/-- Appending one step: the partial mark at `u ++ [i]` is `some` of the
incremented total exactly when `u` is realized and the slot at `i` is present.
This replaces the earlier statement that wrapped the total definition in an
`if`, which forced a `Classical.propDecidable` instance into the conclusion. -/
theorem branchingStepAccumulatedMark?_append_singleton
    {α X : Type*} [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) (i : α) :
    branchingStepAccumulatedMark? step (u ++ [i]) =
        some (branchingStepAccumulatedMark step u + branchingStepIncrement (step u) i) ↔
      branchingRealizedNode step u ∧ branchingStepPresent (step u) i := by
  rw [branchingStepAccumulatedMark?_eq_some_iff, branchingRealizedNode_append_singleton_iff,
    branchingStepAccumulatedMark_append_singleton]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

end ThesisSpeed

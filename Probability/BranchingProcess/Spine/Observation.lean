/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.MeasurableSpace.UniquePresentValue

/-!
# Distinguished-state observations of tagged populations

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `distinguishedState d x` reads the state at the unique distinguished
  coordinate of a tagged population, with default `d` otherwise.
* `distinguishedState_eq` gives `distinguishedState d x = s` when precisely
  one coordinate carries the distinguished state `s`.
* `measurable_distinguishedState` proves measurability for countable index
  spaces and arbitrary measurable ordinary and distinguished states.
* `measurableSet_unique_distinguished` proves measurability of the event
  `∃! i, xᵢ` has the distinguished tag.

These observations apply to arbitrary tagged populations. For their use in
Zhan Shi, *Branching Random Walks* (2015), §4.4, Theorem 4.4(ii), (4.10),
see DOI 10.1007/978-3-319-25372-5. They require no offspring or path law.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory
open scoped ENNReal

/-- Read the unique distinguished state, with a default on exceptional populations. -/
noncomputable def distinguishedState {I S T : Type*} (d : T)
    (x : I → Option (S ⊕ T)) : T :=
  Function.uniquePresentValue d (fun i => (x i).elim none (Sum.elim (fun _ => none) some))

/-- The observation reads the actual state when precisely one coordinate is distinguished. -/
theorem distinguishedState_eq {I S T : Type*} (d : T) (x : I → Option (S ⊕ T))
    (i : I) (s : T) (hi : x i = some (Sum.inr s))
    (ho : ∀ j, j ≠ i → (x j).any Sum.isRight ≠ true) : distinguishedState d x = s := by
  apply Function.uniquePresentValue_eq _ _ i s
  · simp [hi]
  · intro j hji
    have hn := ho j hji
    cases he : x j with
    | none => rfl
    | some a =>
      cases a with
      | inl a => rfl
      | inr a => simp [he] at hn

/-- Countable tagged populations have a measurable distinguished-state observation. -/
@[fun_prop] theorem measurable_distinguishedState {I S T : Type*} [Countable I]
    [MeasurableSpace S] [MeasurableSpace T] (d : T) :
    Measurable (distinguishedState (I := I) (S := S) d) := by
  apply (measurable_uniquePresentValue d).comp
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_option_elim none (measurable_const.sumElim measurable_option_some)).comp
    (measurable_pi_apply i)

/-- The event that a countable tagged population has precisely one distinguished particle. -/
theorem measurableSet_unique_distinguished {I S T : Type*} [Countable I]
    [MeasurableSpace S] [MeasurableSpace T] :
    MeasurableSet {x : I → Option (S ⊕ T) | ∃! i, (x i).any Sum.isRight = true} := by
  have hm : Measurable (fun x : I → Option (S ⊕ T) =>
      fun i => (x i).elim none (Sum.elim (fun _ => none) some)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_option_elim none (measurable_const.sumElim measurable_option_some)).comp
      (measurable_pi_apply i)
  convert measurableSet_unique_present.preimage hm using 1
  ext x
  change (∃! i, (x i).any Sum.isRight = true) ↔
    ∃! i, (x i).elim none (Sum.elim (fun _ => none) some) ≠ none
  have hp (i : I) : (x i).any Sum.isRight = true ↔
      (x i).elim none (Sum.elim (fun _ => none) some) ≠ none := by
    cases x i with
    | none => simp
    | some a => cases a <;> simp
  simp_rw [hp]

end ProbabilityTheory.BranchingProcess.Spine

end

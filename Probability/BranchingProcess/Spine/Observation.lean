/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.MeasurableSpace.Option
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

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
Measurability uses Mathlib's countable-codomain fiber criterion and
countable-index product measurability directly.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory

/-- Read the unique distinguished state, with a default on exceptional populations. -/
noncomputable def distinguishedState {I S T : Type*} (d : T)
    (x : I → Option (S ⊕ T)) : T := by
  classical
  exact if hu : ∃! i, (x i).any Sum.isRight = true then
    (x (Classical.choose hu)).elim d (Sum.elim (fun _ => d) id) else d

/-- The observation reads the actual state when precisely one coordinate is distinguished. -/
theorem distinguishedState_eq {I S T : Type*} (d : T) (x : I → Option (S ⊕ T))
    (i : I) (s : T) (hi : x i = some (Sum.inr s))
    (ho : ∀ j, j ≠ i → (x j).any Sum.isRight ≠ true) : distinguishedState d x = s := by
  classical
  have hu : ∃! j, (x j).any Sum.isRight = true := by
    refine ⟨i, by simp [hi], ?_⟩
    intro j hj
    by_contra hji
    exact ho j hji hj
  rw [distinguishedState, dite_eq_left hu]
  have he : Classical.choose hu = i := hu.unique (Classical.choose_spec hu).1 (by simp [hi])
  simp [he, hi]

/-- The event that a countable tagged population has precisely one distinguished particle. -/
theorem measurableSet_unique_distinguished {I S T : Type*} [Countable I]
    [MeasurableSpace S] [MeasurableSpace T] :
    MeasurableSet {x : I → Option (S ⊕ T) | ∃! i, (x i).any Sum.isRight = true} := by
  classical
  have hp (i : I) : MeasurableSet {x : I → Option (S ⊕ T) |
      (x i).any Sum.isRight = true} :=
    (MeasurableSet.singleton true).preimage
      ((show Measurable (fun o : Option (S ⊕ T) => o.any Sum.isRight) from
        measurable_option_elim false
          (show Measurable (Sum.isRight : S ⊕ T → Bool) from
            measurable_const.sumElim measurable_const)).comp (measurable_pi_apply i))
  change MeasurableSet {x : I → Option (S ⊕ T) | ∃ i,
    (x i).any Sum.isRight = true ∧ ∀ j, (x j).any Sum.isRight = true → j = i}
  rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  rw [Set.ofPred_and]
  apply (hp i).inter
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  by_cases hji : j = i
  · simp [hji]
  · convert (hp j).compl using 1
    ext x
    simp [hji]

/-- Countable tagged populations have a measurable distinguished-state observation. -/
@[fun_prop] theorem measurable_distinguishedState {I S T : Type*} [Countable I]
    [MeasurableSpace S] [MeasurableSpace T] (d : T) :
    Measurable (distinguishedState (I := I) (S := S) d) := by
  classical
  let chosen (x : I → Option (S ⊕ T)) : Option I :=
    if hu : ∃! i, (x i).any Sum.isRight = true then some (Classical.choose hu) else none
  let field (x : I → Option (S ⊕ T)) (i : Option I) : T :=
    i.elim d (fun j => (x j).elim d (Sum.elim (fun _ => d) id))
  have hfiber (i : Option I) : MeasurableSet {x | chosen x = i} := by
    cases i with
    | none =>
      convert (measurableSet_unique_distinguished (I := I) (S := S) (T := T)).compl using 1
      ext x
      simp [chosen]
    | some i =>
      have he : {x | chosen x = some i} =
          {x : I → Option (S ⊕ T) | ∃! j, (x j).any Sum.isRight = true} ∩
            {x | (x i).any Sum.isRight = true} := by
        ext x
        by_cases hu : ∃! j, (x j).any Sum.isRight = true
        · change chosen x = some i ↔
            (∃! j, (x j).any Sum.isRight = true) ∧ (x i).any Sum.isRight = true
          have hc : chosen x = some (Classical.choose hu) := by
            dsimp only [chosen]
            rw [dite_eq_left hu]
          rw [hc]
          simp only [Option.some.injEq, hu, true_and]
          constructor
          · intro he
            rw [← he]
            exact (Classical.choose_spec hu).1
          · intro hi
            exact hu.unique (Classical.choose_spec hu).1 hi
        · simp [chosen, hu]
      rw [he]
      apply measurableSet_unique_distinguished.inter
      exact (MeasurableSet.singleton true).preimage
        ((show Measurable (fun o : Option (S ⊕ T) => o.any Sum.isRight) from
          measurable_option_elim false
            (show Measurable (Sum.isRight : S ⊕ T → Bool) from
              measurable_const.sumElim measurable_const)).comp (measurable_pi_apply i))
  have he : distinguishedState (I := I) (S := S) d = fun x => field x (chosen x) := by
    funext x
    dsimp [distinguishedState, chosen, field]
    split_ifs <;> rfl
  rw [he]
  let _ : MeasurableSpace (Option I) := ⊤
  have hs : Measurable chosen := measurable_to_countable' hfiber
  have hm : Measurable (fun p : (I → Option (S ⊕ T)) × Option I => field p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro i
    cases i with
    | none => exact measurable_const
    | some i =>
      exact (measurable_option_elim d (measurable_const.sumElim measurable_id)).comp
        (measurable_pi_apply i)
  exact hm.comp (measurable_id.prodMk hs)

end ProbabilityTheory.BranchingProcess.Spine

end

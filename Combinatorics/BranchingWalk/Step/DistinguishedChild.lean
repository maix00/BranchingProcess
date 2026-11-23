/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Map

/-!
# Distinguishing one eligible child

## Public declarations

In `Combinatorics.Branching.Step`:

* `distinguishChild P ξ i` changes a family with states in `S` into a family
  with states in `S ⊕ {s // P s}`. Only eligible child `i` is distinguished.
* `distinguishChild_selected` and `distinguishChild_other` identify the selected
  and ordinary slots.
* `distinguishChild_unique` proves that an eligible chosen child is the unique
  distinguished slot: `∃! j, ∃ t, ξ̂(j) = some (inr t)`.
* `distinguishChild_map` states that forgetting the distinction recovers `ξ`.

This deterministic operation is the normal/special-child assignment in
Zhan Shi, *Branching Random Walks* (2015), §4.4 after (4.8),
https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf.
The eligibility predicate and index/state types are arbitrary.
-/

@[expose] public section

namespace Combinatorics.Branching.Step

open scoped Classical

/-- Distinguish the chosen child when eligible; all other children remain ordinary. -/
noncomputable def distinguishChild {ι S : Type*} (P : S → Prop) (ξ : Step ι S) (i : ι) :
    Step ι (S ⊕ {s // P s}) :=
  fun j => (ξ j).map (fun s => if hj : j = i ∧ P s then Sum.inr ⟨s, hj.2⟩ else Sum.inl s)

theorem distinguishChild_selected {ι S : Type*} (P : S → Prop) (ξ : Step ι S)
    (i : ι) {s : S} (hs : ξ i = some s) (hP : P s) :
    distinguishChild P ξ i i = some (Sum.inr ⟨s, hP⟩) := by
  simp [distinguishChild, hs, hP]

theorem distinguishChild_other {ι S : Type*} (P : S → Prop) (ξ : Step ι S)
    (i j : ι) (hji : j ≠ i) :
    distinguishChild P ξ i j = (ξ j).map Sum.inl := by
  cases he : ξ j <;> simp [distinguishChild, he, hji]

/-- An eligible selected child is the unique distinguished slot. -/
theorem distinguishChild_unique {ι S : Type*} (P : S → Prop) (ξ : Step ι S)
    (i : ι) {s : S} (hs : ξ i = some s) (hP : P s) :
    ∃! j, ∃ t : {s // P s}, distinguishChild P ξ i j = some (Sum.inr t) := by
  refine ⟨i, ⟨⟨s, hP⟩, distinguishChild_selected P ξ i hs hP⟩, ?_⟩
  intro j hj
  by_contra hji
  obtain ⟨t, ht⟩ := hj
  rw [distinguishChild_other P ξ i j hji] at ht
  cases he : ξ j <;> simp [he] at ht

/-- Erasing the ordinary/distinguished role recovers the original family exactly. -/
theorem distinguishChild_map {ι S : Type*} (P : S → Prop) (ξ : Step ι S) (i : ι) :
    (distinguishChild P ξ i).map (Sum.elim id Subtype.val) = ξ := by
  funext j
  change Option.map (Sum.elim id Subtype.val)
    ((ξ j).map (fun s => if hj : j = i ∧ P s then Sum.inr ⟨s, hj.2⟩ else Sum.inl s)) = ξ j
  cases he : ξ j with
  | none => rfl
  | some s =>
    by_cases hj : j = i ∧ P s
    · simp only [Option.map_some, dite_eq_left hj, Sum.elim_inr]
    · simp only [Option.map_some, dite_eq_right hj, Sum.elim_inl, id_eq]

end Combinatorics.Branching.Step

end

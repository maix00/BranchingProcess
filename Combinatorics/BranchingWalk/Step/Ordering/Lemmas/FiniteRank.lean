/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Combinatorics.BranchingWalk.Step.Basic
import Mathlib.Data.Finset.Card

/-!
# Finite ranks for ordered child slots

This module contains proof support for
`Step.hasIncreasingEnumeration_of_isFinitelySupported`; it is imported only by
`Step/Ordering/Orderable.lean` and contributes no public API.

## Internal proof declarations

- `below ξ S j` contains the slots in `S` whose mark-slot pair precedes the
  pair at `j`; `rank ξ S j = (below ξ S j).card`.
- `mem_below`, `below_subset_of_below`, and `below_ssubset_of_below` describe
  membership and the strict growth of predecessor sets.
- `rank_injOn`, `rank_lt_card`, and `image_rank_eq_range` show that on finite
  support the rank maps children bijectively to `Finset.range S.card`.
- `exists_some_le_of_rank_le` shows that rank order implies mark order.

The declarations live in `Step.Ordering.Lemmas` and are imported internally
with `import all` by the finite-support normal-form proof.
-/

section

namespace Combinatorics

namespace Branching

namespace Step.Ordering.Lemmas

variable {ι X : Type*} [LinearOrder ι] [LinearOrder X]

/-- The children of a step on a finite set of slots that lie strictly below a given child, compared by
mark first and then by slot: those whose mark is smaller, or equal with a smaller slot. -/
noncomputable def below (ξ : Step ι X) (S : Finset ι) (j : ι) : Finset ι := by
  classical
  exact S.filter fun j' => ∃ x y, ξ j' = some x ∧ ξ j = some y ∧ (x < y ∨ (x = y ∧ j' < j))

lemma mem_below {ξ : Step ι X} {S : Finset ι} {j j' : ι} :
    j' ∈ below ξ S j ↔
      j' ∈ S ∧ ∃ x y, ξ j' = some x ∧ ξ j = some y ∧ (x < y ∨ (x = y ∧ j' < j)) := by
  classical
  exact Finset.mem_filter

/-- A child is not strictly below itself. -/
lemma not_mem_below_self {ξ : Step ι X} {S : Finset ι} {j : ι} :
    j ∉ below ξ S j := by
  classical
  intro h
  obtain ⟨-, x, y, hx, hy, hlt⟩ := mem_below.mp h
  have hxy : x = y := Option.some.inj (by rw [hx] at hy; exact hy)
  rcases hlt with hlt' | ⟨heq, hjj⟩
  · exact absurd hxy (ne_of_lt hlt')
  · exact (lt_irrefl j) hjj

/-- The children strictly below one child are a subset of those strictly below a child that comes later in
the (mark, slot) order. -/
lemma below_subset_of_below {ξ : Step ι X} {S : Finset ι} {j j' : ι}
    (hrel : ∃ x y, ξ j = some x ∧ ξ j' = some y ∧ (x < y ∨ (x = y ∧ j < j'))) :
    below ξ S j ⊆ below ξ S j' := by
  classical
  obtain ⟨xm, ym, hjm, hj'm, hlt⟩ := hrel
  intro a ha
  obtain ⟨haS, xa, xb, hax, hjx, halt⟩ := mem_below.mp ha
  have hb : xb = xm := by
    rw [hjx] at hjm
    exact Option.some.inj hjm
  refine mem_below.mpr ⟨haS, ?_⟩
  rcases halt with hlt' | ⟨heq, haj⟩
  · refine ⟨xa, ym, hax, hj'm, Or.inl ?_⟩
    rcases hlt with hlt'' | ⟨heq', -⟩
    · exact (hb ▸ hlt').trans hlt''
    · exact (hb.trans heq') ▸ hlt'
  · refine ⟨xa, ym, hax, hj'm, ?_⟩
    rcases hlt with hlt'' | ⟨heq', hjj'⟩
    · exact Or.inl ((heq.trans hb).symm ▸ hlt'')
    · exact Or.inr ⟨heq.trans (hb.trans heq'), haj.trans hjj'⟩

/-- The inclusion above is strict: the child itself lies on the right of it. -/
lemma below_ssubset_of_below {ξ : Step ι X} {S : Finset ι} {j j' : ι} (hjS : j ∈ S)
    (hrel : ∃ x y, ξ j = some x ∧ ξ j' = some y ∧ (x < y ∨ (x = y ∧ j < j'))) :
    below ξ S j ⊂ below ξ S j' := by
  classical
  refine ⟨below_subset_of_below hrel, fun hsub => ?_⟩
  have hj' : j ∈ below ξ S j' := mem_below.mpr ⟨hjS, hrel⟩
  exact not_mem_below_self (hsub hj')

/-- The rank of a slot among the children: the number of children strictly below it. -/
noncomputable def rank (ξ : Step ι X) (S : Finset ι) (j : ι) : ℕ :=
  (below ξ S j).card

/-- The rank separates the children of a finite set of slots: two of them with the same rank are the same
slot. The marks are comparable, so one of the two children is strictly below the other in the (mark, slot)
order, which makes its set of children below it a strict subset of the other's. -/
lemma rank_injOn {ξ : Step ι X} {S : Finset ι} (hS : ↑S ⊆ support ξ) :
    Set.InjOn (rank ξ S) ↑S := by
  classical
  intro j hjS j' hj'S h
  by_contra hne
  obtain ⟨x, hx⟩ := hS hjS
  obtain ⟨y, hy⟩ := hS hj'S
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd h (ne_of_lt (Finset.card_lt_card
      (below_ssubset_of_below hjS ⟨x, y, hx, hy, Or.inl hlt⟩)))
  · rcases lt_or_gt_of_ne hne with hjj | hjj
    · exact absurd h (ne_of_lt (Finset.card_lt_card
        (below_ssubset_of_below hjS ⟨x, y, hx, hy, Or.inr ⟨heq, hjj⟩⟩)))
    · exact absurd h.symm (ne_of_lt (Finset.card_lt_card
        (below_ssubset_of_below hj'S ⟨y, x, hy, hx, Or.inr ⟨heq.symm, hjj⟩⟩)))
  · exact absurd h.symm (ne_of_lt (Finset.card_lt_card
      (below_ssubset_of_below hj'S ⟨y, x, hy, hx, Or.inl hgt⟩)))

/-- The rank of a child is smaller than the number of children: the children below it all lie in the
children with it removed. -/
lemma rank_lt_card {ξ : Step ι X} {S : Finset ι} {j : ι} (hjS : j ∈ S) :
    rank ξ S j < S.card := by
  classical
  have hsub : below ξ S j ⊆ S.erase j := by
    intro a ha
    obtain ⟨haS, -⟩ := mem_below.mp ha
    refine Finset.mem_erase.mpr ⟨?_, haS⟩
    intro haj
    exact not_mem_below_self (haj ▸ ha)
  have hle : (below ξ S j).card ≤ (S.erase j).card := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hjS] at hle
  exact lt_of_le_of_lt hle (Nat.sub_one_lt (Finset.card_ne_zero.mpr ⟨j, hjS⟩))

/-- On a finite set of children the rank takes exactly the values below the number of children, so every
label below that number is the rank of one child. -/
lemma image_rank_eq_range {ξ : Step ι X} {S : Finset ι} (hS : ↑S ⊆ support ξ) :
    S.image (rank ξ S) = Finset.range S.card := by
  classical
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro n hn
    obtain ⟨j, hjS, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (rank_lt_card hjS)
  · rw [Finset.card_image_of_injOn (rank_injOn hS), Finset.card_range]

/-- Children ordered by rank are ordered by mark: a child whose rank is no larger than another's cannot
carry the larger mark, since the children below it would then be strictly fewer. -/
lemma exists_some_le_of_rank_le {ξ : Step ι X} {S : Finset ι} (hS : ↑S ⊆ support ξ)
    {a b : ι} (ha : a ∈ S) (hb : b ∈ S) (h : rank ξ S a ≤ rank ξ S b) :
    ∃ x y, ξ a = some x ∧ ξ b = some y ∧ x ≤ y := by
  classical
  obtain ⟨x, hx⟩ := hS ha
  obtain ⟨y, hy⟩ := hS hb
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact ⟨x, y, hx, hy, le_of_lt hlt⟩
  · exact ⟨x, y, hx, hy, le_of_eq heq⟩
  · exact absurd h (not_le_of_gt (Finset.card_lt_card
      (below_ssubset_of_below hb ⟨y, x, hy, hx, Or.inl hgt⟩)))

end Step.Ordering.Lemmas

end Branching

end Combinatorics

end

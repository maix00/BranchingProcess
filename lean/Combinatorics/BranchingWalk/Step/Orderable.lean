import Combinatorics.BranchingWalk.Step.Monotone

/-!
# The orderable form of a finitely supported step

A step with finitely many children can be relabelled into the thesis's normal form: list the children by
increasing mark, ties broken by the slot, and rename the `i`-th of them to `i`; every other slot is sent
outside the children, into the final segment the listing does not use. The listing is not built by
sorting a list — the rank of a child, the number of children strictly below it in the (mark, slot)
lexicographic order, is itself the label, so nothing here depends on a sorting API.

The entries below set up that rank: the children strictly below one child are a subset of those strictly
below a later one, a child is not strictly below itself, and the inclusion is strict.
-/

namespace Combinatorics

namespace Branching

variable {ι X : Type*} [LinearOrder ι] [LinearOrder X]

/-- The children of a step on a finite set of slots that lie strictly below a given child, compared by
mark first and then by slot: those whose mark is smaller, or equal with a smaller slot. -/
noncomputable def Step.below (ξ : Step ι X) (S : Finset ι) (j : ι) : Finset ι := by
  classical
  exact S.filter fun j' => ∃ x y, ξ j' = some x ∧ ξ j = some y ∧ (x < y ∨ (x = y ∧ j' < j))

theorem Step.mem_below {ξ : Step ι X} {S : Finset ι} {j j' : ι} :
    j' ∈ ξ.below S j ↔
      j' ∈ S ∧ ∃ x y, ξ j' = some x ∧ ξ j = some y ∧ (x < y ∨ (x = y ∧ j' < j)) := by
  classical
  exact Finset.mem_filter

/-- A child is not strictly below itself. -/
theorem Step.not_mem_below_self {ξ : Step ι X} {S : Finset ι} {j : ι} :
    j ∉ ξ.below S j := by
  classical
  intro h
  obtain ⟨-, x, y, hx, hy, hlt⟩ := Step.mem_below.mp h
  have hxy : x = y := Option.some.inj (by rw [hx] at hy; exact hy)
  rcases hlt with hlt' | ⟨heq, hjj⟩
  · exact absurd hxy (ne_of_lt hlt')
  · exact (lt_irrefl j) hjj

/-- The children strictly below one child are a subset of those strictly below a child that comes later in
the (mark, slot) order. -/
theorem Step.below_subset_of_below {ξ : Step ι X} {S : Finset ι} {j j' : ι}
    (hrel : ∃ x y, ξ j = some x ∧ ξ j' = some y ∧ (x < y ∨ (x = y ∧ j < j'))) :
    ξ.below S j ⊆ ξ.below S j' := by
  classical
  obtain ⟨xm, ym, hjm, hj'm, hlt⟩ := hrel
  intro a ha
  obtain ⟨haS, xa, xb, hax, hjx, halt⟩ := Step.mem_below.mp ha
  have hb : xb = xm := by
    rw [hjx] at hjm
    exact Option.some.inj hjm
  refine Step.mem_below.mpr ⟨haS, ?_⟩
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
theorem Step.below_ssubset_of_below {ξ : Step ι X} {S : Finset ι} {j j' : ι} (hjS : j ∈ S)
    (hrel : ∃ x y, ξ j = some x ∧ ξ j' = some y ∧ (x < y ∨ (x = y ∧ j < j'))) :
    ξ.below S j ⊂ ξ.below S j' := by
  classical
  refine ⟨Step.below_subset_of_below hrel, fun hsub => ?_⟩
  have hj' : j ∈ ξ.below S j' := Step.mem_below.mpr ⟨hjS, hrel⟩
  exact Step.not_mem_below_self (hsub hj')

/-- The rank of a slot among the children: the number of children strictly below it. -/
noncomputable def Step.rank (ξ : Step ι X) (S : Finset ι) (j : ι) : ℕ :=
  (ξ.below S j).card

/-- The rank separates the children of a finite set of slots: two of them with the same rank are the same
slot. The marks are comparable, so one of the two children is strictly below the other in the (mark, slot)
order, which makes its set of children below it a strict subset of the other's. -/
theorem Step.rank_injOn {ξ : Step ι X} {S : Finset ι} (hS : ↑S ⊆ support ξ) :
    Set.InjOn (ξ.rank S) ↑S := by
  classical
  intro j hjS j' hj'S h
  by_contra hne
  obtain ⟨x, hx⟩ := hS hjS
  obtain ⟨y, hy⟩ := hS hj'S
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd h (ne_of_lt (Finset.card_lt_card
      (Step.below_ssubset_of_below hjS ⟨x, y, hx, hy, Or.inl hlt⟩)))
  · rcases lt_or_gt_of_ne hne with hjj | hjj
    · exact absurd h (ne_of_lt (Finset.card_lt_card
        (Step.below_ssubset_of_below hjS ⟨x, y, hx, hy, Or.inr ⟨heq, hjj⟩⟩)))
    · exact absurd h.symm (ne_of_lt (Finset.card_lt_card
        (Step.below_ssubset_of_below hj'S ⟨y, x, hy, hx, Or.inr ⟨heq.symm, hjj⟩⟩)))
  · exact absurd h.symm (ne_of_lt (Finset.card_lt_card
      (Step.below_ssubset_of_below hj'S ⟨y, x, hy, hx, Or.inl hgt⟩)))

section FinitelySupported

variable {X : Type*} [LinearOrder X]

/-- The rank of a child is smaller than the number of children: the children below it all lie in the
children with it removed. -/
theorem Step.rank_lt_card {ξ : Step ℕ X} {S : Finset ℕ} {j : ℕ} (hjS : j ∈ S) :
    ξ.rank S j < S.card := by
  classical
  have hsub : ξ.below S j ⊆ S.erase j := by
    intro a ha
    obtain ⟨haS, -⟩ := Step.mem_below.mp ha
    refine Finset.mem_erase.mpr ⟨?_, haS⟩
    intro haj
    exact Step.not_mem_below_self (haj ▸ ha)
  have hle : (ξ.below S j).card ≤ (S.erase j).card := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hjS] at hle
  exact lt_of_le_of_lt hle (Nat.sub_one_lt (Finset.card_ne_zero.mpr ⟨j, hjS⟩))

/-- On a finite set of children the rank takes exactly the values below the number of children, so every
label below that number is the rank of one child. -/
theorem Step.image_rank_eq_range {ξ : Step ℕ X} {S : Finset ℕ} (hS : ↑S ⊆ support ξ) :
    S.image (ξ.rank S) = Finset.range S.card := by
  classical
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro n hn
    obtain ⟨j, hjS, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (Step.rank_lt_card hjS)
  · rw [Finset.card_image_of_injOn (Step.rank_injOn hS), Finset.card_range]

end FinitelySupported

end Branching

end Combinatorics

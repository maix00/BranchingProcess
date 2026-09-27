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

end Branching

end Combinatorics

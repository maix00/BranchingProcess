import Combinatorics.UlamHarris.Tree.Graph.Basic
import Mathlib.Combinatorics.Quiver.Arborescence

/-!
# The parent--child quiver is an arborescence

The parent--child quiver of a tree has no repeated edges: the child label is
determined by the parent and the child. It is therefore a thin quiver, and, with
the address length as height, a mathlib `Quiver.Arborescence`: there is a unique
directed path from the root to every realized node. This is the directed form of
the statement that addresses record their unique path from the root.
-/

namespace Combinatorics

namespace UlamHarris

namespace Tree

set_option linter.style.haveILetI false

variable {α : Type*} [LT α]

attribute [local instance] childQuiver

/-- The parent--child quiver has no repeated edges: a child label is determined
by the parent and the child. -/
theorem childQuiver_isThin (T : Tree α) : Quiver.IsThin ↥T.carrier :=
  fun _ _ => ⟨fun e f => Subtype.ext (List.singleton_injective <|
    List.append_cancel_left (e.2.symm.trans f.2))⟩

/-- The parent--child quiver of a tree is a mathlib arborescence: there is a
unique directed path from the root to every realized node. -/
@[instance_reducible]
noncomputable def childQuiver_arborescence (T : Tree α) :
    Quiver.Arborescence ↥T.carrier :=
  Quiver.arborescenceMk ⟨[], T.root_mem⟩ (fun x => x.1.length)
    (by
      rintro a b ⟨i, hi⟩
      exact siblingRel_length_lt ⟨i, hi⟩)
    (by
      rintro a b c e f
      have hab : a = b := Subtype.ext (siblingRel_left_unique ⟨e.1, e.2⟩ ⟨f.1, f.2⟩)
      subst hab
      haveI : Subsingleton (a ⟶ c) := childQuiver_isThin T a c
      exact ⟨rfl, heq_of_eq (Subsingleton.elim e f)⟩)
    (by
      intro b
      rcases eq_or_ne b.1 [] with h | h
      · exact Or.inl (Subtype.ext h)
      · have hmem : b.1.dropLast ∈ T.carrier :=
          mem_parent (u := b.1.dropLast) (v := [b.1.getLast h]) T
            (by rw [List.dropLast_append_getLast h]; exact b.2)
        refine Or.inr ⟨⟨b.1.dropLast, hmem⟩, ⟨b.1.getLast h, ?_⟩⟩
        exact (List.dropLast_append_getLast h).symm)

end Tree

end UlamHarris

end Combinatorics

module

public import Combinatorics.BranchingWalk.MarkedTree.Equivalence
public import Combinatorics.UlamHarris.MarkedTree.SiblingOrder

@[expose] public section

/-!
# Order compatibility for branching walks and marked trees

This adapter identifies monotone child slots with sibling-monotone marks.
The underlying conversions and their round trips live in `Equivalence`.
-/

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris

variable {α X : Type*}

section Order

variable [LT α] [AddCommGroup X] [PartialOrder X] [IsOrderedAddMonoid X]

/-- The order condition of the step at `u` of the field read off a marked tree
is sibling monotonicity of the marks of that tree at `u`: the relative
displacement of a later sibling is at least that of an earlier one exactly when
the marks themselves increase. -/
theorem monotone_stepOfMarkedTree_iff {M : MarkedTree α X} (u : TreeNode α) :
    IsMonotone (stepOfMarkedTree M u) ↔
      ∀ (i j : α)
        (hi : u ++ [i] ∈ M.tree.carrier) (hj : u ++ [j] ∈ M.tree.carrier),
        i < j → M.mark (u ++ [i]) hi ≤ M.mark (u ++ [j]) hj := by
  constructor
  · intro h i j hi hj hij
    have hsame : M.mark u (M.tree.parent_closed hi) =
        M.mark u (M.tree.parent_closed hj) :=
      congrArg (M.mark u) (Subsingleton.elim _ _)
    have hle : M.mark (u ++ [i]) hi - M.mark u (M.tree.parent_closed hi) ≤
        M.mark (u ++ [j]) hj - M.mark u (M.tree.parent_closed hj) :=
      h i j _ _ hij (stepOfMarkedTree_apply_of_mem (M := M) hi)
        (stepOfMarkedTree_apply_of_mem (M := M) hj)
    rw [hsame] at hle
    exact (sub_le_sub_iff_right _).1 hle
  · intro h i j x y hij hx hy
    have hi : u ++ [i] ∈ M.tree.carrier := (survive_stepOfMarkedTree_iff).1 ⟨x, hx⟩
    have hj : u ++ [j] ∈ M.tree.carrier := (survive_stepOfMarkedTree_iff).1 ⟨y, hy⟩
    have hxi : x = M.mark (u ++ [i]) hi - M.mark u (M.tree.parent_closed hi) := by
      rw [stepOfMarkedTree_apply_of_mem (M := M) hi] at hx
      exact (Option.some.inj hx).symm
    have hxj : y = M.mark (u ++ [j]) hj - M.mark u (M.tree.parent_closed hj) := by
      rw [stepOfMarkedTree_apply_of_mem (M := M) hj] at hy
      exact (Option.some.inj hy).symm
    have hsame : M.mark u (M.tree.parent_closed hi) =
        M.mark u (M.tree.parent_closed hj) :=
      congrArg (M.mark u) (Subsingleton.elim _ _)
    rw [hxi, hxj, hsame]
    exact (sub_le_sub_iff_right _).2 (h i j hi hj hij)

/-- The field read off a marked tree is ordered exactly when the tree is
sibling monotone. -/
theorem forall_monotone_stepOfMarkedTree_iff {M : MarkedTree α X} :
    (∀ u, IsMonotone (stepOfMarkedTree M u)) ↔ M.siblingMonotone := by
  simp only [MarkedTree.siblingMonotone, monotone_stepOfMarkedTree_iff]

/-- Marking an ordered step field gives a sibling-monotone marked tree, because
the ordering condition says that the survive marks increase along the slot
order. -/
theorem siblingMonotone_markedTreeOfStep (step : StepField α X)
    (hsibling : IsSiblingClosed step)
    (hmono : ∀ u, IsMonotone (step u)) :
    (markedTreeOfStep step hsibling).siblingMonotone := by
  intro u i j hi hj hij
  show displace step [] (u ++ [i]) ≤ displace step [] (u ++ [j])
  obtain ⟨-, hi'⟩ := (surviveAlong_root_append_singleton_iff step u i).1 hi
  obtain ⟨-, hj'⟩ := (surviveAlong_root_append_singleton_iff step u j).1 hj
  obtain ⟨a, ha⟩ := hi'
  obtain ⟨b, hb⟩ := hj'
  have hle : a ≤ b := hmono u i j a b hij ha hb
  rw [displace_append_singleton, value'_some _ _ _ ha,
    displace_append_singleton, value'_some _ _ _ hb]
  exact add_le_add_right hle _

end Order


end Branching

end Combinatorics

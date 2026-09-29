module

public import Combinatorics.UlamHarris.Tree.RootIndexed.Graph.IsTree
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# The single-tree case of the forest projection

For a one-element root index type the forest of a root-indexed tree is one tree,
so its graph is the child graph of that tree. `uniqueForestGraphIso` is the
graph isomorphism, and the two specialization statements below say that the
`Tree` versions `Tree.childGraph_isAcyclic` and `Tree.childGraph_isTree` are
exactly the one-root case of the forest versions.

The dependency direction stays the one of `RootIndexed.Tree/Basic.lean`, where a
root-indexed tree is defined from `Tree`; the forest results are the general ones
and the single-tree results are their one-root instance.
-/

@[expose] public section

namespace Combinatorics

namespace UlamHarris

namespace RootIndexed.Tree

variable {Root α : Type*} [LT α] [Unique Root]

/-- The forest of a one-root family is the child graph of its only tree. -/
def uniqueForestGraphIso (T : RootIndexed.Tree Root α) :
    forestGraph T ≃g Tree.childGraph (T default) where
  toFun x := ⟨x.1.2, by simpa [Unique.eq_default x.1.1] using x.2⟩
  invFun y := ⟨(default, y.1), y.2⟩
  left_inv x := Subtype.ext (Prod.ext (Unique.eq_default x.1.1).symm rfl)
  right_inv y := Subtype.ext rfl
  map_rel_iff' := by
    intro a b
    simp only [forestGraph_adj, Tree.childGraph_adj]
    exact ⟨fun h => ⟨(Unique.eq_default a.1.1).trans (Unique.eq_default b.1.1).symm, h⟩,
      fun h => h.2⟩

/-- The tree version of acyclicity is the one-root case of the forest version. -/
theorem childGraph_isAcyclic_iff_forestGraph (T : RootIndexed.Tree Root α) :
    (Tree.childGraph (T default)).IsAcyclic ↔ (forestGraph T).IsAcyclic :=
  (uniqueForestGraphIso T).isAcyclic_iff.symm

/-- The tree version of connectivity is the one-root case of the forest version. -/
theorem childGraph_connected_iff_forestGraph (T : RootIndexed.Tree Root α) :
    (Tree.childGraph (T default)).Connected ↔ (forestGraph T).Connected :=
  (uniqueForestGraphIso T).connected_iff.symm

/-- The tree version of being a tree is the one-root case of the forest version. -/
theorem childGraph_isTree_iff_forestGraph (T : RootIndexed.Tree Root α) :
    (Tree.childGraph (T default)).IsTree ↔ (forestGraph T).IsTree :=
  (uniqueForestGraphIso T).isTree_iff.symm

end RootIndexed.Tree

end UlamHarris

end Combinatorics

end

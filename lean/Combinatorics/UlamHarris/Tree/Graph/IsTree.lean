module

public import Combinatorics.UlamHarris.Tree.Graph.Acyclic
public import Combinatorics.UlamHarris.Tree.Graph.Connected
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# The projected graph of a tree is a tree

Combining connectivity (`Graph/Connected.lean`) with acyclicity
(`Graph/Acyclic.lean`), the underlying undirected simple graph of a
deterministic Ulam--Harris tree is a mathlib `SimpleGraph.IsTree`.

This is the check that the projection really produces a tree: the address space
`Tree α` is only a carrier with axioms, and `Tree.childGraph` maps it onto
mathlib's notion of a tree on an arbitrary vertex type.
-/

@[expose] public section

namespace Combinatorics

namespace UlamHarris

namespace Tree

variable {α : Type*} [LT α]

/-- The underlying undirected graph of a tree is a mathlib tree. -/
theorem childGraph_isTree (T : Tree α) : (childGraph T).IsTree :=
  ⟨childGraph_connected T, childGraph_isAcyclic T⟩

end Tree

namespace RootIndexed.Tree

set_option linter.style.haveILetI false

variable {Root α : Type*} [LT α]

/-- The forest projection is a mathlib tree exactly in the one-root case. -/
theorem forestGraph_isTree (T : RootIndexed.Tree Root α) [Unique Root] :
    (forestGraph T).IsTree := by
  haveI : Nonempty Root := ⟨default⟩
  haveI : Subsingleton Root :=
    ⟨fun a b => (Unique.eq_default a).trans (Unique.eq_default b).symm⟩
  exact ⟨forestGraph_connected T, forestGraph_isAcyclic T⟩

end RootIndexed.Tree

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
    exact ⟨fun h => ⟨(Unique.eq_default a.1.1).trans
        (Unique.eq_default b.1.1).symm, h⟩, fun h => h.2⟩

theorem childGraph_isAcyclic_iff_forestGraph (T : RootIndexed.Tree Root α) :
    (Tree.childGraph (T default)).IsAcyclic ↔ (forestGraph T).IsAcyclic :=
  (uniqueForestGraphIso T).isAcyclic_iff.symm

theorem childGraph_connected_iff_forestGraph (T : RootIndexed.Tree Root α) :
    (Tree.childGraph (T default)).Connected ↔ (forestGraph T).Connected :=
  (uniqueForestGraphIso T).connected_iff.symm

theorem childGraph_isTree_iff_forestGraph (T : RootIndexed.Tree Root α) :
    (Tree.childGraph (T default)).IsTree ↔ (forestGraph T).IsTree :=
  (uniqueForestGraphIso T).isTree_iff.symm

end RootIndexed.Tree

end UlamHarris

end Combinatorics

end

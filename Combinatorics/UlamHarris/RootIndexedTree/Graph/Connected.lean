import Combinatorics.UlamHarris.RootIndexedTree.Graph.Basic
import Combinatorics.UlamHarris.Tree.Graph.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connectivity of the forest of a root-indexed tree

A walk in the forest stays inside one tree of the family, and inside one tree the
root reaches every realized node (`Tree.childGraph_reachable`). So the forest is
connected exactly in the one-tree case, when the root index type is a
subsingleton. With several trees the components are separate, and the forest is
not a tree.
-/

namespace Combinatorics

namespace UlamHarris

namespace RootIndexedTree

variable {Root α : Type*} [LT α]

/-- A walk of the child graph of one tree is a walk of the forest, in the same
tree of the family. -/
private def forestWalkOfTreeWalk (T : RootIndexedTree Root α) (r : Root)
    {a b : ↥(T r).carrier} (p : (Tree.childGraph (T r)).Walk a b) :
    (forestGraph T).Walk ⟨(r, a.1), a.2⟩ ⟨(r, b.1), b.2⟩ :=
  match p with
  | .nil => .nil
  | .cons h p => .cons ((forestGraph_adj_mk_iff a _).2 h) (forestWalkOfTreeWalk T r p)

/-- Inside one tree of the family, its root reaches every realized node. -/
theorem forestGraph_reachable_same_root (T : RootIndexedTree Root α) (r : Root)
    (b : ↥(T r).carrier) :
    (forestGraph T).Reachable ⟨(r, []), (T r).root_mem⟩ ⟨(r, b.1), b.2⟩ :=
  ⟨forestWalkOfTreeWalk T r (Tree.childGraph_reachable (T r) b).some⟩

/-- With a single tree the forest is preconnected: any two realized vertices lie
in that one tree and are joined through its root. -/
theorem forestGraph_preconnected (T : RootIndexedTree Root α) [Subsingleton Root] :
    (forestGraph T).Preconnected := by
  intro a b
  have hroot : (⟨(b.1.1, []), (T b.1.1).root_mem⟩ : ForestVertex T) =
      ⟨(a.1.1, []), (T a.1.1).root_mem⟩ :=
    Subtype.ext (Prod.ext (Subsingleton.elim b.1.1 a.1.1) rfl)
  exact (forestGraph_reachable_same_root T a.1.1 ⟨a.1.2, a.2⟩).symm.trans
    ⟨(forestGraph_reachable_same_root T b.1.1 ⟨b.1.2, b.2⟩).some.copy hroot rfl⟩

/-- With at least two trees the forest is not preconnected: no walk leaves one
tree of the family for another. -/
theorem not_forestGraph_preconnected {T : RootIndexedTree Root α} {r s : Root}
    (h : r ≠ s) : ¬ (forestGraph T).Preconnected := by
  intro hpre
  exact h (forestGraph_reachable_root_eq (T := T)
    (hpre ⟨(r, []), (T r).root_mem⟩ ⟨(s, []), (T s).root_mem⟩))

/-- The forest is preconnected exactly when the family has a single tree, that
is when the root index type is a subsingleton. -/
theorem forestGraph_preconnected_iff_subsingleton (T : RootIndexedTree Root α) :
    (forestGraph T).Preconnected ↔ Subsingleton Root := by
  refine ⟨fun h => ⟨fun r s => ?_⟩, fun h => ?_⟩
  · by_contra hrs
    exact not_forestGraph_preconnected hrs h
  · have hsub : Subsingleton Root := h
    exact forestGraph_preconnected T

/-- The forest of a one-tree family is connected. -/
theorem forestGraph_connected (T : RootIndexedTree Root α)
    [Nonempty Root] [Subsingleton Root] : (forestGraph T).Connected where
  preconnected := forestGraph_preconnected T
  nonempty := ⟨⟨(Classical.arbitrary Root, []), (T (Classical.arbitrary Root)).root_mem⟩⟩

end RootIndexedTree

end UlamHarris

end Combinatorics

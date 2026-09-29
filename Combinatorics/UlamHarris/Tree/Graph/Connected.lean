module

public import Combinatorics.UlamHarris.Tree.Graph.Arborescence
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# The projected graph of a tree is connected

Every realized node is the endpoint of a unique directed path from the root in
the parent--child quiver. The same sequence of edges is a walk in the underlying
simple graph, so the root reaches every realized node, and by symmetry and
transitivity the graph is connected.
-/

@[expose] public section

namespace Combinatorics

namespace UlamHarris

namespace Tree

set_option linter.style.haveILetI false

variable {α : Type*} [LT α]

attribute [local instance] childQuiver

/-- Every quiver path in the parent--child quiver is a walk in the underlying
simple graph. -/
private def walkOfPath (T : Tree α) {a b : ↥T.carrier} (p : Quiver.Path a b) :
    (childGraph T).Walk a b :=
  match p with
  | .nil => .nil
  | .cons p e =>
      (walkOfPath T p).concat ((childGraph_adj (T := T)).2 (Or.inl ⟨e.1, e.2⟩))

/-- In the underlying undirected graph, the root reaches every realized node. -/
theorem childGraph_reachable (T : Tree α) (b : ↥T.carrier) :
    (childGraph T).Reachable ⟨[], T.root_mem⟩ b := by
  letI : Quiver.Arborescence ↥T.carrier := childQuiver_arborescence T
  have hroot : (Quiver.Arborescence.root : ↥T.carrier) = ⟨[], T.root_mem⟩ := rfl
  exact ⟨(walkOfPath T (Quiver.Arborescence.uniquePath b).default).copy hroot rfl⟩

/-- The underlying undirected graph is preconnected. -/
theorem childGraph_preconnected (T : Tree α) : (childGraph T).Preconnected :=
  fun a b => (childGraph_reachable T a).symm.trans (childGraph_reachable T b)

/-- The underlying undirected graph of a tree is connected. -/
theorem childGraph_connected (T : Tree α) : (childGraph T).Connected where
  preconnected := childGraph_preconnected T
  nonempty := ⟨⟨[], T.root_mem⟩⟩

end Tree

namespace RootIndexed.Tree

variable {Root α : Type*} [LT α]

private def forestWalkOfTreeWalk (T : RootIndexed.Tree Root α) (r : Root)
    {a b : ↥(T r).carrier} (p : (Tree.childGraph (T r)).Walk a b) :
    (forestGraph T).Walk ⟨(r, a.1), a.2⟩ ⟨(r, b.1), b.2⟩ :=
  match p with
  | .nil => .nil
  | .cons h p => .cons ((forestGraph_adj_mk_iff a _).2 h)
      (forestWalkOfTreeWalk T r p)

theorem forestGraph_reachable_same_root (T : RootIndexed.Tree Root α) (r : Root)
    (b : ↥(T r).carrier) :
    (forestGraph T).Reachable ⟨(r, []), (T r).root_mem⟩ ⟨(r, b.1), b.2⟩ :=
  ⟨forestWalkOfTreeWalk T r (Tree.childGraph_reachable (T r) b).some⟩

theorem forestGraph_preconnected (T : RootIndexed.Tree Root α) [Subsingleton Root] :
    (forestGraph T).Preconnected := by
  intro a b
  have hroot : (⟨(b.1.1, []), (T b.1.1).root_mem⟩ : ForestVertex T) =
      ⟨(a.1.1, []), (T a.1.1).root_mem⟩ :=
    Subtype.ext (Prod.ext (Subsingleton.elim b.1.1 a.1.1) rfl)
  exact (forestGraph_reachable_same_root T a.1.1 ⟨a.1.2, a.2⟩).symm.trans
    ⟨(forestGraph_reachable_same_root T b.1.1 ⟨b.1.2, b.2⟩).some.copy hroot rfl⟩

theorem not_forestGraph_preconnected {T : RootIndexed.Tree Root α} {r s : Root}
    (h : r ≠ s) : ¬ (forestGraph T).Preconnected := by
  intro hpre
  exact h (forestGraph_reachable_root_eq (T := T)
    (hpre ⟨(r, []), (T r).root_mem⟩ ⟨(s, []), (T s).root_mem⟩))

theorem forestGraph_preconnected_iff_subsingleton (T : RootIndexed.Tree Root α) :
    (forestGraph T).Preconnected ↔ Subsingleton Root := by
  refine ⟨fun h => ⟨fun r s => ?_⟩, fun h => ?_⟩
  · by_contra hrs
    exact not_forestGraph_preconnected hrs h
  · have hsub : Subsingleton Root := h
    exact forestGraph_preconnected T

theorem forestGraph_connected (T : RootIndexed.Tree Root α)
    [Nonempty Root] [Subsingleton Root] : (forestGraph T).Connected where
  preconnected := forestGraph_preconnected T
  nonempty := ⟨⟨(Classical.arbitrary Root, []),
    (T (Classical.arbitrary Root)).root_mem⟩⟩

end RootIndexed.Tree

end UlamHarris

end Combinatorics

end

import Combinatorics.UlamHarris.Tree.Graph.Arborescence
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# The projected graph of a tree is connected

Every realized node is the endpoint of a unique directed path from the root in
the parent--child quiver. The same sequence of edges is a walk in the underlying
simple graph, so the root reaches every realized node, and by symmetry and
transitivity the graph is connected.
-/

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

end UlamHarris

end Combinatorics

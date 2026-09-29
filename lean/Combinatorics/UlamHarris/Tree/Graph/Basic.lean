module

public import Combinatorics.UlamHarris.Tree.Basic
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Graph projections of a tree

`Tree α` is a set of addresses with axioms, not a mathlib graph: mathlib's
graph objects live on a vertex type, while a tree carries its own vertex set.
This folder projects the carrier of a tree onto the mathlib objects that model
rooted trees on an *arbitrary* vertex type, with no countability or finiteness
hypothesis. Every projection is built from the one address-level parent
relation `Tree.siblingRel` of `Tree/Basic.lean`.

* `Tree.childDigraph` is the directed parent--child graph `Digraph ↥T.carrier`,
  mathlib's Prop-valued relation form (`Mathlib/Combinatorics/Digraph/Basic.lean`),
  which is the recommended form when there are no repeated edges.
* `Tree.childQuiver` is the same relation as a quiver, whose homs are the child
  labels. Thinness and the arborescence structure are in `Graph/Arborescence.lean`.
* `Tree.childGraph` is the underlying undirected simple graph, the
  symmetrization of the parent relation. Connectivity is in `Graph/Connected.lean`,
  acyclicity in `Graph/Acyclic.lean`, and `Graph/IsTree.lean` puts the two
  together into `SimpleGraph.IsTree`.

The multigraph `Graph α β` of `Mathlib/Combinatorics/Graph/Basic.lean` is not
used: a node of a tree has at most one edge to each child, so its parent--child
structure is already carried faithfully by a digraph.
-/

@[expose] public section

namespace Combinatorics

namespace UlamHarris

namespace Tree

variable {α : Type*} [LT α]

/-- The directed parent--child graph on the realized carrier. -/
def childDigraph (T : Tree α) : Digraph ↥T.carrier where
  Adj a b := siblingRel a.1 b.1

/-- A vertex of the child digraph is never adjacent to itself. -/
theorem childDigraph_adj_irrefl (T : Tree α) (a : ↥T.carrier) :
    ¬ (childDigraph T).Adj a a :=
  siblingRel_irrefl a.1

/-- The parent--child quiver on the realized carrier: an arrow from `a` to `b`
is a child label `i` with `b = a ++ [i]`. -/
@[instance_reducible]
def childQuiver (T : Tree α) : Quiver ↥T.carrier where
  Hom a b := {i : α // b.1 = a.1 ++ [i]}

attribute [local instance] childQuiver

@[simp]
theorem childQuiver_hom_iff {T : Tree α} {a b : ↥T.carrier} :
    Nonempty (a ⟶ b) ↔ (childDigraph T).Adj a b :=
  ⟨fun ⟨e⟩ => ⟨e.1, e.2⟩, fun ⟨i, hi⟩ => ⟨⟨i, hi⟩⟩⟩

/-- The underlying undirected simple graph on the realized carrier: two nodes
are adjacent when one is the parent of the other. -/
def childGraph (T : Tree α) : SimpleGraph ↥T.carrier :=
  SimpleGraph.fromRel (childDigraph T).Adj

/-- Adjacency in the directed graph is the parent relation, in one direction. -/
theorem childDigraph_adj_iff {T : Tree α} {a b : ↥T.carrier} :
    (childDigraph T).Adj a b ↔ siblingRel a.1 b.1 :=
  Iff.rfl

/-- Adjacency in the undirected graph is the parent relation in one of the two
directions. -/
@[simp]
theorem childGraph_adj {T : Tree α} {a b : ↥T.carrier} :
    (childGraph T).Adj a b ↔ siblingRel a.1 b.1 ∨ siblingRel b.1 a.1 := by
  rw [childGraph, SimpleGraph.fromRel_adj]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rintro rfl
  exact h.elim (childDigraph_adj_irrefl T a) (childDigraph_adj_irrefl T a)

end Tree

end UlamHarris

end Combinatorics

end

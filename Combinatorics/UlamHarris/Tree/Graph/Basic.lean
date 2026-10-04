/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Relation
public import Combinatorics.UlamHarris.Tree.Defs
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Graph projections of a tree

`Tree α` is a set of addresses with axioms, not a mathlib graph: mathlib's
graph objects live on a vertex type, while a tree carries its own vertex set.
This folder projects the carrier of a tree onto the mathlib objects that model
rooted trees on an *arbitrary* vertex type, with no countability or finiteness
hypothesis. Every projection is built from the address-level parent-to-child
relation `TreeNode.IsChild` in `Combinatorics.UlamHarris.Relation`.

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
  Adj a b := TreeNode.IsChild a.1 b.1

/-- A vertex of the child digraph is never adjacent to itself. -/
theorem childDigraph_adj_irrefl (T : Tree α) (a : ↥T.carrier) :
    ¬ (childDigraph T).Adj a a :=
  TreeNode.IsChild.irrefl a.1

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
    (childDigraph T).Adj a b ↔ TreeNode.IsChild a.1 b.1 :=
  Iff.rfl

/-- Adjacency in the undirected graph is the parent relation in one of the two
directions. -/
@[simp]
theorem childGraph_adj {T : Tree α} {a b : ↥T.carrier} :
    (childGraph T).Adj a b ↔
      TreeNode.IsChild a.1 b.1 ∨ TreeNode.IsChild b.1 a.1 := by
  rw [childGraph, SimpleGraph.fromRel_adj]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rintro rfl
  exact h.elim (childDigraph_adj_irrefl T a) (childDigraph_adj_irrefl T a)

end Tree

namespace RootIndexed.Tree

variable {Root α : Type*} [LT α]

/-- The vertices of the forest of a root-indexed tree: realized pairs of a
root index and an address. -/
abbrev ForestVertex (T : RootIndexed.Tree Root α) : Type _ :=
  {p : RootIndexed.TreeNode Root α // p.2 ∈ (T p.1).carrier}

/-- The disjoint union of the child graphs of all root coordinates. -/
def forestGraph (T : RootIndexed.Tree Root α) : SimpleGraph (ForestVertex T) where
  Adj a b := a.1.1 = b.1.1 ∧
    (TreeNode.IsChild a.1.2 b.1.2 ∨ TreeNode.IsChild b.1.2 a.1.2)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun a h => h.2.elim (TreeNode.IsChild.irrefl a.1.2)
    (TreeNode.IsChild.irrefl a.1.2)⟩

@[simp]
theorem forestGraph_adj {T : RootIndexed.Tree Root α} {a b : ForestVertex T} :
    (forestGraph T).Adj a b ↔
      a.1.1 = b.1.1 ∧
        (TreeNode.IsChild a.1.2 b.1.2 ∨ TreeNode.IsChild b.1.2 a.1.2) :=
  Iff.rfl

theorem forestGraph_adj_mk_iff {T : RootIndexed.Tree Root α} {r : Root}
    (a b : ↥(T r).carrier) :
    (forestGraph T).Adj ⟨(r, a.1), a.2⟩ ⟨(r, b.1), b.2⟩ ↔
      (Tree.childGraph (T r)).Adj a b := by
  rw [forestGraph_adj, Tree.childGraph_adj]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem forestGraph_walk_root_eq {T : RootIndexed.Tree Root α} {a b : ForestVertex T}
    (p : (forestGraph T).Walk a b) : a.1.1 = b.1.1 := by
  induction p with
  | nil => rfl
  | cons h p ih => exact h.1.trans ih

theorem forestGraph_reachable_root_eq {T : RootIndexed.Tree Root α} {a b : ForestVertex T}
    (h : (forestGraph T).Reachable a b) : a.1.1 = b.1.1 :=
  h.elim fun p => forestGraph_walk_root_eq p

end RootIndexed.Tree

end UlamHarris

end Combinatorics

end

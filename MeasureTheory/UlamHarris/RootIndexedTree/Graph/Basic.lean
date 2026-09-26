import MeasureTheory.UlamHarris.RootIndexedTree.Basic
import MeasureTheory.UlamHarris.Tree.Graph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# The forest of a root-indexed tree

`RootIndexedTree Root α` is a family of trees, one for each initial ancestor, so
its graph projection is a forest: the disjoint union of the child graphs
`Tree.childGraph (T r)`. Unlike a single tree the general object is neither
connected nor a mathlib `SimpleGraph.IsTree`; it is acyclic
(`Graph/Acyclic.lean`), it is connected in the one-root case
(`Graph/Connected.lean`), and `Graph/Singleton.lean` records that the `Tree`
version of every graph statement is exactly that one-root case.

Vertices are presented inside `Root × TreeNode α` as the realized pairs `(r, u)`
with `u ∈ (T r).carrier`. Keeping the root index and the address as the two
components avoids dependent casts: adjacency is the address-level
`Tree.parentRel`, restricted to pairs with the same root index, which is the same
relation the single-tree projections use.
-/

namespace MeasureTheory

namespace UlamHarris

namespace RootIndexedTree

variable {Root α : Type*} [LT α]

/-- The vertex set of the forest of a root-indexed tree: the disjoint union of
the realized carriers, presented inside `Root × TreeNode α`. -/
abbrev ForestVertex (T : RootIndexedTree Root α) : Type _ :=
  {p : Root × TreeNode α // p.2 ∈ (T p.1).carrier}

/-- The forest of a root-indexed tree: the disjoint union of the child graphs of
its trees. Two realized vertices are adjacent when they share their root index
and one address is the parent of the other. -/
def forestGraph (T : RootIndexedTree Root α) : SimpleGraph (ForestVertex T) where
  Adj a b := a.1.1 = b.1.1 ∧ (Tree.parentRel a.1.2 b.1.2 ∨ Tree.parentRel b.1.2 a.1.2)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun a h => h.2.elim (Tree.parentRel_irrefl a.1.2) (Tree.parentRel_irrefl a.1.2)⟩

@[simp]
theorem forestGraph_adj {T : RootIndexedTree Root α} {a b : ForestVertex T} :
    (forestGraph T).Adj a b ↔
      a.1.1 = b.1.1 ∧ (Tree.parentRel a.1.2 b.1.2 ∨ Tree.parentRel b.1.2 a.1.2) :=
  Iff.rfl

/-- Inside one tree of the family, adjacency of the forest is adjacency of the
child graph of that tree. -/
theorem forestGraph_adj_mk_iff {T : RootIndexedTree Root α} {r : Root}
    (a b : ↥(T r).carrier) :
    (forestGraph T).Adj ⟨(r, a.1), a.2⟩ ⟨(r, b.1), b.2⟩ ↔
      (Tree.childGraph (T r)).Adj a b := by
  rw [forestGraph_adj, Tree.childGraph_adj]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

/-- A walk in the forest stays inside one tree of the family. -/
theorem forestGraph_walk_root_eq {T : RootIndexedTree Root α} {a b : ForestVertex T}
    (p : (forestGraph T).Walk a b) : a.1.1 = b.1.1 := by
  induction p with
  | nil => rfl
  | cons h p ih => exact h.1.trans ih

/-- Reachability in the forest respects the root index: the trees of the family
have no edge between them. -/
theorem forestGraph_reachable_root_eq {T : RootIndexedTree Root α} {a b : ForestVertex T}
    (h : (forestGraph T).Reachable a b) : a.1.1 = b.1.1 :=
  h.elim fun p => forestGraph_walk_root_eq p

end RootIndexedTree

end UlamHarris

end MeasureTheory

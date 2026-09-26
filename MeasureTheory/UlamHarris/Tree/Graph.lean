import MeasureTheory.UlamHarris.Tree.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Quiver.Arborescence
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Graph projections of a tree

`Tree α` is a set of addresses with axioms, not a mathlib graph: mathlib's graph
objects live on a vertex type, while a tree carries its own vertex set. This
file projects a tree onto the mathlib objects that model rooted trees on an
*arbitrary* vertex type, with no countability or finiteness hypothesis:

* `Tree.childDigraph` is the directed parent-child graph `Digraph ↥T.carrier`,
  mathlib's Prop-valued relation form (`Mathlib/Combinatorics/Digraph/Basic.lean`),
  which is the recommended form when there are no repeated edges.
* `Tree.childQuiver` is the same relation as a quiver, whose homs are the child
  labels; `Tree.childQuiver_isThin` records that it has no repeated edges and
  `Tree.childQuiver_arborescence` that it is a `Quiver.Arborescence`: there is a
  unique directed path from the root to every realized node
  (`Mathlib/Combinatorics/Quiver/Arborescence.lean`).
* `Tree.childGraph` is the underlying undirected simple graph, the symmetrization
  `SimpleGraph.fromRel` of the child relation, and `Tree.childGraph_reachable`
  says the root reaches every realized node.

The multigraph `Graph α β` of `Mathlib/Combinatorics/Graph/Basic.lean` is not
used: a node of a tree has at most one edge to each child, so its parent-child
structure is already carried faithfully by a digraph.
-/

namespace MeasureTheory

namespace UlamHarris

namespace Tree

set_option linter.style.haveILetI false

variable {α : Type*}

/-- The child relation on addresses: `b` is obtained from `a` by appending the
label `i`. It is stated on raw addresses; a tree selects which of them are
realized. -/
def childRel (a b : List α) : Prop :=
  ∃ i : α, b = a ++ [i]

@[simp]
theorem childRel_def (a b : List α) :
    childRel a b ↔ ∃ i : α, b = a ++ [i] :=
  Iff.rfl

theorem childRel_lt {a b : List α} (h : childRel a b) : a.length < b.length := by
  rcases h with ⟨i, rfl⟩
  simp [List.length_append]

/-- Two children of the same address have the same parent. -/
theorem childRel_parent_injective {a b c : List α}
    (hab : childRel a c) (hbc : childRel b c) : a = b := by
  rcases hab with ⟨i, rfl⟩
  rcases hbc with ⟨j, hj⟩
  have h := congrArg List.dropLast hj
  simpa using h

variable [LT α]

/-- The directed parent-child graph on the realized carrier. -/
def childDigraph (T : Tree α) : Digraph ↥T.carrier where
  Adj a b := childRel a.1 b.1

/-- The parent-child quiver on the realized carrier: an arrow from `a` to `b`
is a child label `i` with `b = a ++ [i]`. -/
@[instance_reducible]
def childQuiver (T : Tree α) : Quiver ↥T.carrier where
  Hom a b := {i : α // b.1 = a.1 ++ [i]}

attribute [local instance] childQuiver

@[simp]
theorem childQuiver_hom_iff {T : Tree α} {a b : ↥T.carrier} :
    Nonempty (a ⟶ b) ↔ (childDigraph T).Adj a b :=
  ⟨fun ⟨e⟩ => ⟨e.1, e.2⟩, fun ⟨i, hi⟩ => ⟨⟨i, hi⟩⟩⟩

/-- The parent-child quiver has no repeated edges: a child label is determined
by the parent and the child. -/
theorem childQuiver_isThin (T : Tree α) : Quiver.IsThin ↥T.carrier :=
  fun _ _ => ⟨fun e f => Subtype.ext (List.singleton_injective <|
    List.append_cancel_left (e.2.symm.trans f.2))⟩

/-- The parent-child quiver of a tree is a mathlib arborescence: there is a
unique directed path from the root to every realized node. -/
@[instance_reducible]
noncomputable def childQuiver_arborescence (T : Tree α) :
    Quiver.Arborescence ↥T.carrier :=
  Quiver.arborescenceMk ⟨[], T.root_mem⟩ (fun x => x.1.length)
    (by
      rintro a b ⟨i, hi⟩
      exact childRel_lt ⟨i, hi⟩)
    (by
      rintro a b c e f
      have hab : a = b := Subtype.ext (childRel_parent_injective ⟨e.1, e.2⟩ ⟨f.1, f.2⟩)
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

/-- The underlying undirected simple graph on the realized carrier: two nodes
are adjacent when one is the child of the other. -/
def childGraph (T : Tree α) : SimpleGraph ↥T.carrier :=
  SimpleGraph.fromRel (childDigraph T).Adj

@[simp]
theorem childGraph_adj {T : Tree α} {a b : ↥T.carrier} :
    (childGraph T).Adj a b ↔ (childDigraph T).Adj a b ∨ (childDigraph T).Adj b a := by
  rw [childGraph, SimpleGraph.fromRel_adj]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rintro rfl
  rcases h with h | h
  · exact absurd (childRel_lt h) (lt_irrefl _)
  · exact absurd (childRel_lt h) (lt_irrefl _)

/-- Every quiver path in the parent-child quiver is a walk in the underlying
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

end Tree

end UlamHarris

end MeasureTheory

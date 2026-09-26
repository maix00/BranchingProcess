import MeasureTheory.UlamHarris.Tree.Graph.Basic
import MeasureTheory.UlamHarris.Graph.Height
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The projected graph of a tree is acyclic

The address length is a height on the underlying undirected graph of a tree:
adjacent nodes have different lengths, and every node has at most one parent
(`Tree.parentRel_left_unique`). The shared height criterion
`SimpleGraph.isAcyclic_of_height` then gives acyclicity.
-/

namespace MeasureTheory

namespace UlamHarris

namespace Tree

variable {α : Type*} [LT α]

/-- Adjacent nodes of the child graph have different address lengths. -/
theorem childGraph_adj_length_ne {T : Tree α} {a b : ↥T.carrier}
    (h : (childGraph T).Adj a b) : a.1.length ≠ b.1.length := by
  rcases childGraph_adj.mp h with h | h
  · exact (parentRel_length_lt h).ne
  · exact (parentRel_length_lt h).ne'

/-- The first endpoint of an edge of smaller length is the parent. -/
theorem parentRel_of_childGraph_adj_of_length_lt {T : Tree α} {a b : ↥T.carrier}
    (h : (childGraph T).Adj a b) (hlt : a.1.length < b.1.length) : parentRel a.1 b.1 := by
  rcases childGraph_adj.mp h with h' | h'
  · exact h'
  · exact absurd (parentRel_length_lt h') (not_lt.mpr hlt.le)

/-- The underlying undirected graph of a tree is acyclic. -/
theorem childGraph_isAcyclic (T : Tree α) : (childGraph T).IsAcyclic := by
  refine SimpleGraph.isAcyclic_of_height (childGraph T) (fun v => v.1.length) ?_
  intro a b c hac hbc ha hb
  exact Subtype.ext (parentRel_left_unique
    (parentRel_of_childGraph_adj_of_length_lt hac
      (lt_of_le_of_ne ha (childGraph_adj_length_ne hac)))
    (parentRel_of_childGraph_adj_of_length_lt hbc
      (lt_of_le_of_ne hb (childGraph_adj_length_ne hbc))))

end Tree

end UlamHarris

end MeasureTheory

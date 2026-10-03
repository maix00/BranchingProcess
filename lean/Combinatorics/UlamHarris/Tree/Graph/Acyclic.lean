module

public import Combinatorics.UlamHarris.Tree.Graph.Basic
public import Combinatorics.SimpleGraph.Acyclic.Height
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The projected graph of a tree is acyclic

The address length is a height on the underlying undirected graph of a tree:
adjacent nodes have different lengths, and every node has at most one parent
(`TreeNode.IsChild.parent_unique`). The shared height criterion
`SimpleGraph.isAcyclic_of_height` then gives acyclicity.
-/

@[expose] public section

namespace Combinatorics

namespace UlamHarris

namespace Tree

variable {α : Type*} [LT α]

/-- Adjacent nodes of the child graph have different address lengths. -/
theorem childGraph_adj_length_ne {T : Tree α} {a b : ↥T.carrier}
    (h : (childGraph T).Adj a b) : a.1.length ≠ b.1.length := by
  rcases childGraph_adj.mp h with h | h
  · exact (TreeNode.IsChild.length_lt h).ne
  · exact (TreeNode.IsChild.length_lt h).ne'

/-- The first endpoint of an edge of smaller length is the parent. -/
theorem isChild_of_childGraph_adj_of_length_lt {T : Tree α} {a b : ↥T.carrier}
    (h : (childGraph T).Adj a b) (hlt : a.1.length < b.1.length) :
    TreeNode.IsChild a.1 b.1 := by
  rcases childGraph_adj.mp h with h' | h'
  · exact h'
  · exact absurd (TreeNode.IsChild.length_lt h') (not_lt.mpr hlt.le)

/-- The underlying undirected graph of a tree is acyclic. -/
theorem childGraph_isAcyclic (T : Tree α) : (childGraph T).IsAcyclic := by
  refine SimpleGraph.isAcyclic_of_height (childGraph T) (fun v => v.1.length) ?_
  intro a b c hac hbc ha hb
  exact Subtype.ext (TreeNode.IsChild.parent_unique
    (isChild_of_childGraph_adj_of_length_lt hac
      (lt_of_le_of_ne ha (childGraph_adj_length_ne hac)))
    (isChild_of_childGraph_adj_of_length_lt hbc
      (lt_of_le_of_ne hb (childGraph_adj_length_ne hbc))))

end Tree

namespace RootIndexed.Tree

variable {Root α : Type*} [LT α]

/-- The forest of a root-indexed tree is acyclic, regardless of the number of
initial ancestors. -/
theorem forestGraph_isAcyclic (T : RootIndexed.Tree Root α) :
    (forestGraph T).IsAcyclic := by
  refine SimpleGraph.isAcyclic_of_height (forestGraph T) (fun v => v.1.2.length) ?_
  intro a b c hac hbc ha hb
  have ha' : TreeNode.IsChild a.1.2 c.1.2 := by
    rcases hac.2 with h' | h'
    · exact h'
    · exact absurd (TreeNode.IsChild.length_lt h') (not_lt.mpr ha)
  have hb' : TreeNode.IsChild b.1.2 c.1.2 := by
    rcases hbc.2 with h' | h'
    · exact h'
    · exact absurd (TreeNode.IsChild.length_lt h') (not_lt.mpr hb)
  exact Subtype.ext (Prod.ext (hac.1.trans hbc.1.symm)
    (TreeNode.IsChild.parent_unique ha' hb'))

end RootIndexed.Tree

end UlamHarris

end Combinatorics

end

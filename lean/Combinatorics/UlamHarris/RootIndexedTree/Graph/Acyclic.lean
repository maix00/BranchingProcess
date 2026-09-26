import Combinatorics.SimpleGraph.Acyclic.Height
import Combinatorics.UlamHarris.RootIndexedTree.Graph.Basic

/-!
# The forest of a root-indexed tree is acyclic

The address length is a height on the whole forest, and every vertex has at most
one neighbour whose address is no longer than its own: a neighbour lies in the
same tree of the family, and there it is either the parent or a child. The shared
height criterion `SimpleGraph.isAcyclic_of_height` therefore applies. This is the
forest-level version of `Tree.childGraph_isAcyclic`, and the tree version is its
one-root case (`Graph/Singleton.lean`).
-/

namespace Combinatorics

namespace UlamHarris

namespace RootIndexed.Tree

variable {Root α : Type*} [LT α]

/-- The forest of a root-indexed tree is acyclic, however many trees it has. -/
theorem forestGraph_isAcyclic (T : RootIndexed.Tree Root α) :
    (forestGraph T).IsAcyclic := by
  refine SimpleGraph.isAcyclic_of_height (forestGraph T) (fun v => v.1.2.length) ?_
  intro a b c hac hbc ha hb
  have ha' : Tree.siblingRel a.1.2 c.1.2 := by
    rcases hac.2 with h' | h'
    · exact h'
    · exact absurd (Tree.siblingRel_length_lt h') (not_lt.mpr ha)
  have hb' : Tree.siblingRel b.1.2 c.1.2 := by
    rcases hbc.2 with h' | h'
    · exact h'
    · exact absurd (Tree.siblingRel_length_lt h') (not_lt.mpr hb)
  exact Subtype.ext (Prod.ext (hac.1.trans hbc.1.symm) (Tree.siblingRel_left_unique ha' hb'))

end RootIndexed.Tree

end UlamHarris

end Combinatorics

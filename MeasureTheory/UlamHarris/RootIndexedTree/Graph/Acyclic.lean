import MeasureTheory.UlamHarris.Graph.Height
import MeasureTheory.UlamHarris.RootIndexedTree.Graph.Basic

/-!
# The forest of a root-indexed tree is acyclic

The address length is a height on the whole forest, and every vertex has at most
one neighbour whose address is no longer than its own: a neighbour lies in the
same tree of the family, and there it is either the parent or a child. The shared
height criterion `SimpleGraph.isAcyclic_of_height` therefore applies. This is the
forest-level version of `Tree.childGraph_isAcyclic`, and the tree version is its
one-root case (`Graph/Singleton.lean`).
-/

namespace MeasureTheory

namespace UlamHarris

namespace RootIndexedTree

variable {Root α : Type*} [LT α]

/-- The forest of a root-indexed tree is acyclic, however many trees it has. -/
theorem forestGraph_isAcyclic (T : RootIndexedTree Root α) :
    (forestGraph T).IsAcyclic := by
  refine SimpleGraph.isAcyclic_of_height (forestGraph T) (fun v => v.1.2.length) ?_
  intro a b c hac hbc ha hb
  have ha' : Tree.parentRel a.1.2 c.1.2 := by
    rcases hac.2 with h' | h'
    · exact h'
    · exact absurd (Tree.parentRel_length_lt h') (not_lt.mpr ha)
  have hb' : Tree.parentRel b.1.2 c.1.2 := by
    rcases hbc.2 with h' | h'
    · exact h'
    · exact absurd (Tree.parentRel_length_lt h') (not_lt.mpr hb)
  exact Subtype.ext (Prod.ext (hac.1.trans hbc.1.symm) (Tree.parentRel_left_unique ha' hb'))

end RootIndexedTree

end UlamHarris

end MeasureTheory

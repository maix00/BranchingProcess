import Combinatorics.UlamHarris.Tree.RootIndexed.Graph.Acyclic
import Combinatorics.UlamHarris.Tree.RootIndexed.Graph.Connected

/-!
# The forest of a one-root family is a tree

Connectivity (`Graph/Connected.lean`) holds exactly when the family has one
tree, and acyclicity (`Graph/Acyclic.lean`) holds always. So the graph
projection of a root-indexed tree is a mathlib `SimpleGraph.IsTree` precisely in
the one-root case.
-/

namespace Combinatorics

namespace UlamHarris

namespace RootIndexed.Tree

set_option linter.style.haveILetI false

variable {Root α : Type*} [LT α]

/-- The forest of a family with one initial ancestor is a mathlib tree. -/
theorem forestGraph_isTree (T : RootIndexed.Tree Root α) [Unique Root] :
    (forestGraph T).IsTree := by
  haveI : Nonempty Root := ⟨default⟩
  haveI : Subsingleton Root :=
    ⟨fun a b => (Unique.eq_default a).trans (Unique.eq_default b).symm⟩
  exact ⟨forestGraph_connected T, forestGraph_isAcyclic T⟩

end RootIndexed.Tree

end UlamHarris

end Combinatorics

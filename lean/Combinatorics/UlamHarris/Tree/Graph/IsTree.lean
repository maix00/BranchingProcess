import Combinatorics.UlamHarris.Tree.Graph.Acyclic
import Combinatorics.UlamHarris.Tree.Graph.Connected

/-!
# The projected graph of a tree is a tree

Combining connectivity (`Graph/Connected.lean`) with acyclicity
(`Graph/Acyclic.lean`), the underlying undirected simple graph of a
deterministic Ulam--Harris tree is a mathlib `SimpleGraph.IsTree`.

This is the check that the projection really produces a tree: the address space
`Tree α` is only a carrier with axioms, and `Tree.childGraph` maps it onto
mathlib's notion of a tree on an arbitrary vertex type.
-/

namespace Combinatorics

namespace UlamHarris

namespace Tree

variable {α : Type*} [LT α]

/-- The underlying undirected graph of a tree is a mathlib tree. -/
theorem childGraph_isTree (T : Tree α) : (childGraph T).IsTree :=
  ⟨childGraph_connected T, childGraph_isAcyclic T⟩

end Tree

end UlamHarris

end Combinatorics

module

public import Combinatorics.UlamHarris.MarkedTree.Measurability

/-!
# Forgetting the marks of a marked tree

`MarkedTree α X` pairs a tree with a mark on each realized node, so forgetting
the marks is the projection on the tree. This is the single-root case of the
connection from marked trees to trees; the root-indexed version is in
`UlamHarris/RootIndexed.MarkedTree/Forget.lean`.

The map is measurable for the σ-algebras induced by the tree and by the pair
`(tree, mark?)`, because the tree is one of the coordinates.
-/

@[expose] public section

namespace Combinatorics

namespace UlamHarris

namespace MarkedTree

variable {α X : Type*} [LT α]

/-- Forget the marks of a marked tree, keeping its tree. -/
def forgetMark (M : MarkedTree α X) : Tree α := M.tree

@[simp] theorem forgetMark_apply (M : MarkedTree α X) :
    M.forgetMark = M.tree := rfl

@[simp] theorem forgetMark_carrier (M : MarkedTree α X) :
    M.forgetMark.carrier = M.tree.carrier := rfl

@[simp] theorem forgetMark_root_mem (M : MarkedTree α X) :
    [] ∈ M.forgetMark.carrier := M.tree.root_mem

section Measurable

variable [MeasurableSpace X]

/-- Forgetting the marks is measurable: the tree is one of the coordinates that
induce the σ-algebra on marked trees. -/
theorem measurable_forgetMark :
    Measurable (forgetMark (α := α) (X := X)) :=
  UlamHarris.measurable_tree

end Measurable

end MarkedTree

end UlamHarris

end Combinatorics

end

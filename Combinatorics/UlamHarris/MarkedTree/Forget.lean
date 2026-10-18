/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.MarkedTree.Measurability
public import Combinatorics.UlamHarris.MarkedTree.Singleton
public import Combinatorics.UlamHarris.Tree.Singleton

/-!
# Forgetting the marks of a marked tree

`MarkedTree α X` pairs a tree with a mark on each realized node, so forgetting
the marks is the projection on the tree. This is the single-root case of the
connection from marked trees to trees; the root-indexed counterpart is below
in the `RootIndexed.MarkedTree` namespace.

The map is measurable for the σ-algebras induced by the tree and by the pair
`(tree, mark?)`, because the tree is one of the coordinates.

The public declarations are:

* `Combinatorics.UlamHarris.MarkedTree.forgetMark` is the projection
  `M ↦ M.tree`; `Combinatorics.UlamHarris.MarkedTree.forgetMark_apply` and
  `Combinatorics.UlamHarris.MarkedTree.forgetMark_carrier` state the
  definitional tree and carrier equalities, and
  `Combinatorics.UlamHarris.MarkedTree.forgetMark_root_mem` states
  `[] ∈ M.forgetMark.carrier`.
* Under `[MeasurableSpace X]`,
  `Combinatorics.UlamHarris.MarkedTree.measurable_forgetMark` states that
  `M ↦ M.forgetMark` is measurable.
* `Combinatorics.UlamHarris.RootIndexed.MarkedTree.forgetMark` applies the
  projection at every root;
  `Combinatorics.UlamHarris.RootIndexed.MarkedTree.forgetMark_apply` and
  `Combinatorics.UlamHarris.RootIndexed.MarkedTree.forgetMark_eq_tree` give
  its coordinate and family equations.
  `Combinatorics.UlamHarris.RootIndexed.MarkedTree.forgetMark_comp` states
  that `forgetMark (M ∘ f) = forgetMark M ∘ f` for every root map `f`.
* Under `[MeasurableSpace X]`,
  `Combinatorics.UlamHarris.RootIndexed.MarkedTree.measurable_forgetMark`
  states measurability of the family projection.
* Under `[Unique Root]`,
  `Combinatorics.UlamHarris.RootIndexed.MarkedTree.forgetMark_equivOfUnique`
  identifies the family projection with the single-tree projection through
  the unique-root equivalences.
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

namespace RootIndexed.MarkedTree

variable {Root NewRoot α X : Type*} [LT α]

/-- Forget the marks of every tree of a root-indexed marked family, keeping the
family of trees. -/
def forgetMark (M : RootIndexed.MarkedTree Root α X) : RootIndexed.Tree Root α :=
  fun r => (M r).forgetMark

@[simp]
theorem forgetMark_apply (M : RootIndexed.MarkedTree Root α X) (r : Root) :
    M.forgetMark r = (M r).forgetMark := rfl

/-- Forgetting the marks of a family is the realized-tree map that the family
already carries. -/
@[simp] theorem forgetMark_eq_tree (M : RootIndexed.MarkedTree Root α X) :
    M.forgetMark = M.tree := rfl

/-- The forgetful map commutes with precomposition of the root index. -/
@[simp]
theorem forgetMark_comp (M : RootIndexed.MarkedTree Root α X)
    (f : NewRoot → Root) :
    forgetMark (M ∘ f) = forgetMark M ∘ f := rfl

section Measurable

variable [MeasurableSpace X]

/-- Forgetting the marks of a root-indexed family is measurable. -/
theorem measurable_forgetMark :
    Measurable (forgetMark (Root := Root) (α := α) (X := X)) := by
  rw [measurable_pi_iff]
  intro r
  exact UlamHarris.measurable_tree.comp (measurable_apply r)

end Measurable

section Unique

variable [Unique Root]

/-- The forgetful map of families is the forgetful map of marked trees under
the one-root identifications. -/
theorem forgetMark_equivOfUnique (M : RootIndexed.MarkedTree Root α X) :
    RootIndexed.Tree.equivOfUnique (forgetMark M) =
      UlamHarris.MarkedTree.forgetMark (equivOfUnique M) := rfl

end Unique

end RootIndexed.MarkedTree

end UlamHarris

end Combinatorics

end

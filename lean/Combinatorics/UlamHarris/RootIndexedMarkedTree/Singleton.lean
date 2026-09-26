import Combinatorics.UlamHarris.RootIndexedMarkedTree.Measurability

/-!
# The single-root case of a root-indexed marked tree

`RootIndexedMarkedTree Root α X` is an indexed family of `MarkedTree α X`
(`Basic.lean`), so a family over a one-element index type *is* a marked tree.
For `[Unique Root]`, `equivOfUnique` identifies `RootIndexedMarkedTree Root α X`
with `MarkedTree α X`, and the identification preserves the measurable space
(`measurableSpace_eq_comap`). In particular `MarkedTree α X` is
`RootIndexedMarkedTree Unit α X` and `RootIndexedMarkedTree (Fin 1) α X`. As for
`RootIndexedTree`, the multi-root object is defined from the single-root one.
-/

open MeasureTheory

namespace Combinatorics

namespace UlamHarris

namespace RootIndexedMarkedTree

variable {Root α X : Type*} [LT α]

section Unique

variable [Unique Root]

/-- A root-indexed marked tree over a single initial ancestor is a marked
tree. -/
def equivOfUnique : RootIndexedMarkedTree Root α X ≃ MarkedTree α X :=
  Equiv.funUnique Root (MarkedTree α X)

@[simp]
theorem equivOfUnique_apply (M : RootIndexedMarkedTree Root α X) :
    equivOfUnique (Root := Root) (α := α) (X := X) M = M default :=
  rfl

@[simp]
theorem equivOfUnique_symm_apply (M : MarkedTree α X) :
    (equivOfUnique (Root := Root) (α := α) (X := X)).symm M = fun _ => M :=
  rfl

section Measurable

variable [MeasurableSpace X]

/-- The measurable space of a single-root marked family is the marked tree
σ-algebra of its only initial ancestor. -/
theorem measurableSpace_eq_comap :
    (inferInstance : MeasurableSpace (RootIndexedMarkedTree Root α X)) =
      (inferInstance : MeasurableSpace (MarkedTree α X)).comap
        (equivOfUnique (Root := Root) (α := α) (X := X)) := by
  rw [measurableSpace_eq_iSup, iSup_unique]
  rfl

end Measurable

end Unique

end RootIndexedMarkedTree

end UlamHarris

end Combinatorics

module

public import Combinatorics.UlamHarris.MarkedTree.Measurability

/-!
# The single-root case of root-indexed marked trees

`RootIndexed.MarkedTree Root α X` is an indexed family of
`UlamHarris.MarkedTree α X`.  When `Root` has one element this family is
identified with the single marked tree.  The multi-root definition itself is
in `MarkedTree/Basic.lean`; this file only records the specialization.
-/

open MeasureTheory

@[expose] public section

namespace Combinatorics

namespace UlamHarris

namespace RootIndexed.MarkedTree

variable {Root α X : Type*} [LT α]

section Unique

variable [Unique Root]

/-- A root-indexed marked tree over one initial ancestor is a marked tree. -/
def equivOfUnique : RootIndexed.MarkedTree Root α X ≃ UlamHarris.MarkedTree α X :=
  Equiv.funUnique Root (UlamHarris.MarkedTree α X)

@[simp]
theorem equivOfUnique_apply (M : RootIndexed.MarkedTree Root α X) :
    equivOfUnique (Root := Root) (α := α) (X := X) M = M default :=
  rfl

@[simp]
theorem equivOfUnique_symm_apply (M : UlamHarris.MarkedTree α X) :
    (equivOfUnique (Root := Root) (α := α) (X := X)).symm M = fun _ => M :=
  rfl

section Measurable

variable [MeasurableSpace X]

/-- The measurable space of a one-root marked family is the marked-tree
σ-algebra of its only initial ancestor. -/
theorem measurableSpace_eq_comap :
    (inferInstance : MeasurableSpace (RootIndexed.MarkedTree Root α X)) =
      (inferInstance : MeasurableSpace (UlamHarris.MarkedTree α X)).comap
        (equivOfUnique (Root := Root) (α := α) (X := X)) := by
  rw [measurableSpace_eq_iSup, iSup_unique]
  rfl

end Measurable

end Unique

end RootIndexed.MarkedTree

end UlamHarris

end Combinatorics

end

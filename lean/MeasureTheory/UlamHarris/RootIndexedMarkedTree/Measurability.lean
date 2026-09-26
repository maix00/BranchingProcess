import MeasureTheory.UlamHarris.RootIndexedMarkedTree.Basic
import MeasureTheory.UlamHarris.Tree.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Measurability of root-indexed marked trees

`RootIndexedMarkedTree Root α X` carries the product σ-algebra of the marked
tree σ-algebras. The coordinate projections to the tree and to every mark
reading are measurable, and a map into root-indexed marked trees is measurable
exactly when all of those coordinates are measurable.
-/

open MeasureTheory

namespace MeasureTheory

namespace UlamHarris

namespace RootIndexedMarkedTree

variable {Root α X : Type*} [LT α] [MeasurableSpace X]

/-- The measurable space of a root-indexed marked tree is the product of the
marked tree σ-algebras of the initial ancestors. -/
theorem measurableSpace_eq_iSup :
    (inferInstance : MeasurableSpace (RootIndexedMarkedTree Root α X)) =
      ⨆ r : Root,
        MeasurableSpace.comap
          (fun M : RootIndexedMarkedTree Root α X => M r) inferInstance :=
  rfl

/-- Each initial ancestor of a root-indexed marked tree is separately
measurable. -/
theorem measurable_apply (r : Root) :
    Measurable (fun M : RootIndexedMarkedTree Root α X => M r) :=
  measurable_pi_apply r

/-- The realized tree of a fixed initial ancestor is measurable. -/
theorem measurable_tree (r : Root) :
    Measurable (fun M : RootIndexedMarkedTree Root α X => M.tree r) :=
  (UlamHarris.measurable_tree (α := α) (X := X)).comp (measurable_apply r)

/-- The `Option`-valued mark of a fixed initial ancestor at a fixed address is
measurable. -/
theorem measurable_mark? (r : Root) (u : List α) :
    Measurable (fun M : RootIndexedMarkedTree Root α X => M.mark? r u) :=
  (UlamHarris.measurable_mark? (α := α) (X := X) u).comp (measurable_apply r)

/-- Membership of a fixed address in the realized tree of a fixed initial
ancestor is measurable. -/
theorem measurableSet_tree_carrier (r : Root) (u : List α) :
    MeasurableSet {M : RootIndexedMarkedTree Root α X | u ∈ (M.tree r).carrier} :=
  (UlamHarris.measurableSet_tree_carrier (α := α) (X := X) u).preimage
    (measurable_apply r)

/-- A map into root-indexed marked trees is measurable exactly when every
coordinate marked tree is measurable. -/
theorem measurable_iff_forall {β : Type*} [MeasurableSpace β]
    (f : β → RootIndexedMarkedTree Root α X) :
    Measurable f ↔ ∀ r, Measurable (fun x => f x r) :=
  measurable_pi_iff

/-- A map into root-indexed marked trees is measurable exactly when, for every
initial ancestor, its realized tree and all of its mark readings are
measurable. -/
theorem measurable_iff_forall_tree_mark? {β : Type*} [MeasurableSpace β]
    (f : β → RootIndexedMarkedTree Root α X) :
    Measurable f ↔
      ∀ r, Measurable (fun x => ((f x).tree r, (f x).mark? r)) := by
  rw [measurable_iff_forall]
  constructor
  · intro hf r
    exact (UlamHarris.measurable_tree_mark? (α := α) (X := X)).comp (hf r)
  · intro hf r
    exact measurable_comap_iff.2 (hf r)

end RootIndexedMarkedTree

end UlamHarris

end MeasureTheory

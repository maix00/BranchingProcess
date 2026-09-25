import MeasureTheory.UlamHarris.Tree.Basic
import MeasureTheory.BranchingWalk.Basic
import Mathlib.Data.PFun

/-!
# Marked Ulam--Harris trees

`MarkedTree α X` pairs a realized tree `Tree α` with a mark in `X` on every
realized node; it is the object meant when one says "marked tree". The marks
are defined only on a part of the address space, so they are exposed as the
partial function `partialMark : TreeNode α →. X` and the `Option`-valued
accessor `mark? : TreeNode α → Option X`. Neither view needs a `?`-suffixed
*type*: `?` names functions returning `Option`.

The measurable space on `MarkedTree α X` is induced by the pair
`M ↦ (M.tree, M.mark?)`: the tree carries the tree σ-algebra and `mark?` reads
the marks through the coordinate σ-algebra of `TreeNode α → Option X`, where
`Option X` carries the disjoint-union σ-algebra. Thus both the realized
carrier and every mark are measurable coordinates.
-/

namespace MeasureTheory

namespace UlamHarris

/-- A realized tree together with a mark on each of its realized nodes. This
is the object meant when one says "marked tree"; it is not the full address
field. -/
structure MarkedTree (α X : Type*) [LT α] where
  tree : Tree α
  mark : (u : List α) → u ∈ tree.carrier → X

namespace MarkedTree

variable {α X : Type*} [LT α]

/-- The mark at the root. -/
def rootMark (T : MarkedTree α X) : X := T.mark [] T.tree.root_mem

@[simp] theorem rootMark_eq (T : MarkedTree α X) :
    T.rootMark = T.mark [] T.tree.root_mem := rfl

/-! The marks of a `MarkedTree` are defined only on the realized nodes, that
is, on a part of the address space. Mathlib represents a function whose domain
is only part of a type as a partial function `α →. β = α → Part β`
(`Mathlib/Data/PFun.lean`); accessors returning `Option` carry the `?` suffix
(`List.get?`). Both views are provided below. -/

/-- The marks of a marked tree as a partial function on addresses, defined
exactly on the realized nodes. -/
def partialMark (T : MarkedTree α X) : (List α) →. X :=
  fun u => ⟨u ∈ T.tree.carrier, fun h => T.mark u h⟩

/-- The domain of `partialMark` is the realized tree. -/
@[simp] theorem partialMark_dom (T : MarkedTree α X) :
    T.partialMark.Dom = T.tree.carrier := rfl

/-- Evaluating `partialMark` at a realized node returns the mark of that
node. -/
@[simp] theorem partialMark_asSubtype (T : MarkedTree α X) (u : List α)
    (h : u ∈ T.tree.carrier) : T.partialMark.asSubtype ⟨u, h⟩ = T.mark u h :=
  rfl

/-- The marks of a marked tree as an `Option`-valued function of addresses:
`some` on a realized node and `none` elsewhere. This is the `?` convention of
mathlib for partial accessors (`List.get?`); it is the `Option` view of
`partialMark`. -/
noncomputable def mark? (T : MarkedTree α X) : List α → Option X := by
  classical
  exact fun u => if h : u ∈ T.tree.carrier then some (T.mark u h) else none

@[simp] theorem mark?_apply_mem (T : MarkedTree α X) {u : List α}
    (h : u ∈ T.tree.carrier) : T.mark? u = some (T.mark u h) := by
  classical
  simp [mark?, h]

@[simp] theorem mark?_apply_notMem (T : MarkedTree α X) {u : List α}
    (h : u ∉ T.tree.carrier) : T.mark? u = none := by
  classical
  simp [mark?, h]

end MarkedTree

/-- The measurable space on marked trees, induced by the tree together with
the `Option`-valued mark reading. -/
noncomputable instance instMeasurableSpaceMarkedTree {α X : Type*} [LT α]
    [MeasurableSpace X] : MeasurableSpace (MarkedTree α X) :=
  MeasurableSpace.comap (fun T : MarkedTree α X => (T.tree, T.mark?))
    inferInstance

theorem measurable_tree_mark? {α X : Type*} [LT α] [MeasurableSpace X] :
    Measurable (fun T : MarkedTree α X => (T.tree, T.mark?)) :=
  Measurable.of_comap_le le_rfl

theorem measurable_tree {α X : Type*} [LT α] [MeasurableSpace X] :
    Measurable (fun T : MarkedTree α X => T.tree) :=
  measurable_fst.comp measurable_tree_mark?

theorem measurable_mark? {α X : Type*} [LT α] [MeasurableSpace X]
    (u : List α) :
    Measurable (fun T : MarkedTree α X => T.mark? u) :=
  (measurable_pi_apply u).comp (measurable_snd.comp measurable_tree_mark?)

/-- Membership of a fixed address in the realized tree is measurable. -/
theorem measurableSet_tree_carrier {α X : Type*} [LT α] [MeasurableSpace X]
    (u : List α) :
    MeasurableSet {T : MarkedTree α X | u ∈ T.tree.carrier} :=
  MeasurableSet.preimage (measurableSet_carrier (α := α) u) measurable_tree

end UlamHarris

end MeasureTheory

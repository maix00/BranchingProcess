import MeasureTheory.UlamHarris.MarkedTree.Basic
import MeasureTheory.UlamHarris.Tree.Basic
import MeasureTheory.BranchingWalk.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Measurability of marked Ulam--Harris trees

The measurable space on `MarkedTree α X` is induced by the pair
`M ↦ (M.tree, M.mark?)`: the tree carries the tree σ-algebra and `mark?` reads
the marks through the coordinate σ-algebra of `TreeNode α → Option X`, where
`Option X` carries the disjoint-union σ-algebra. Thus both the realized
carrier and every mark are measurable coordinates.
-/

open MeasureTheory

namespace MeasureTheory

namespace UlamHarris

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

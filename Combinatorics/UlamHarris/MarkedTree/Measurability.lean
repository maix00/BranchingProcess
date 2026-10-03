module

public import Combinatorics.UlamHarris.MarkedTree.Basic
public import Combinatorics.UlamHarris.Tree.MeasurableSpace
public import Combinatorics.BranchingWalk.Step.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Measurability of marked Ulam--Harris trees

The measurable space on `MarkedTree α X` is induced by the pair
`M ↦ (M.tree, M.mark?)`: the tree carries the tree σ-algebra and `mark?` reads
the marks through the coordinate σ-algebra of `TreeNode α → Option X`, where
`Option X` carries the disjoint-union σ-algebra. Thus both the realized
carrier and every mark are measurable coordinates.
-/

@[expose] public section

open MeasureTheory

namespace Combinatorics

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

namespace RootIndexed.MarkedTree

variable {Root α X : Type*} [LT α] [MeasurableSpace X]

/-- The measurable space of a root-indexed marked tree is the product of the
marked-tree σ-algebras of the initial ancestors. -/
theorem measurableSpace_eq_iSup :
    (inferInstance : MeasurableSpace (RootIndexed.MarkedTree Root α X)) =
      ⨆ r : Root,
        MeasurableSpace.comap
          (fun M : RootIndexed.MarkedTree Root α X => M r) inferInstance :=
  rfl

/-- Each initial ancestor of a root-indexed marked tree is separately
measurable. -/
theorem measurable_apply (r : Root) :
    Measurable (fun M : RootIndexed.MarkedTree Root α X => M r) :=
  measurable_pi_apply r

/-- The realized tree of a fixed initial ancestor is measurable. -/
theorem measurable_tree (r : Root) :
    Measurable (fun M : RootIndexed.MarkedTree Root α X => M.tree r) :=
  (UlamHarris.measurable_tree (α := α) (X := X)).comp (measurable_apply r)

/-- The `Option`-valued mark of a fixed initial ancestor at a fixed address is
measurable. -/
theorem measurable_mark? (r : Root) (u : List α) :
    Measurable (fun M : RootIndexed.MarkedTree Root α X => M.mark? r u) :=
  (UlamHarris.measurable_mark? (α := α) (X := X) u).comp (measurable_apply r)

/-- Membership of a fixed address in a fixed root's realized tree is
measurable. -/
theorem measurableSet_tree_carrier (r : Root) (u : List α) :
    MeasurableSet {M : RootIndexed.MarkedTree Root α X | u ∈ (M r).tree.carrier} :=
  MeasurableSet.preimage (UlamHarris.measurableSet_tree_carrier (α := α) (X := X) u)
    (measurable_apply r)

/-- A map into a root-indexed marked tree is measurable when every root
coordinate is measurable. -/
theorem measurable_iff_forall {β : Type*} [MeasurableSpace β]
    (f : β → RootIndexed.MarkedTree Root α X) :
    Measurable f ↔ ∀ r, Measurable (fun x => f x r) :=
  measurable_pi_iff

/-- Coordinatewise measurability of every tree and mark is equivalent to
measurability of a map into root-indexed marked trees. -/
theorem measurable_iff_forall_tree_mark? {β : Type*} [MeasurableSpace β]
    (f : β → RootIndexed.MarkedTree Root α X) :
    Measurable f ↔
      ∀ r, Measurable (fun x => ((f x).tree r, (f x).mark? r)) := by
  rw [measurable_iff_forall]
  constructor
  · intro hf r
    exact (UlamHarris.measurable_tree_mark? (α := α) (X := X)).comp (hf r)
  · intro hf r
    exact measurable_comap_iff.2 (hf r)

end RootIndexed.MarkedTree

end UlamHarris

end Combinatorics

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Cloud.Order.Slice

/-!
# Domination order on a cloud

`Cloud.Dominates C D` is the slice order of `Cloud/Order/Slice.lean` at every
time, on the Dirac sums of the two populations: at every time and threshold, `C`
has no more particles weakly below the threshold than `D`, counting multiplicity.

The other direction of the line is the same definition read in `OrderDual`, which
`dominates_orderDual_iff` displays in the upper-tail form of B\'erard and
Gou\'er\'e. It is *not* `Dominates` with the two clouds exchanged, because both
directions keep the particle count of the first cloud below that of the second.
-/

open MeasureTheory

open Combinatorics.UlamHarris

@[expose] public section

namespace Combinatorics

namespace Branching

variable {Time Root α X : Type*}

/-- `C` dominates `D` when it dominates `D` in every time slice, on the counting
measures of the two populations. -/
def Cloud.Dominates [MeasurableSpace X] [Preorder X]
    (C D : Cloud Time Root α X) : Prop :=
  ∀ t : Time, SliceDominatesMeasure (C.diracSum t) (D.diracSum t)

/-- Domination through an ordered measurable observation of the position
space. The underlying positions need no order and need not be real-valued.
In the one-dimensional model this is `φ = id`; for a directional or potential
frontier it is the chosen scalar observation. -/
def Cloud.DominatesBy {Position Value : Type*}
    [MeasurableSpace Value] [Preorder Value]
    (φ : Position → Value) (C D : Cloud Time Root α Position) : Prop :=
  (C.mapPosition φ).Dominates (D.mapPosition φ)

theorem Cloud.dominates_iff [MeasurableSpace X] [Preorder X]
    (C D : Cloud Time Root α X) :
    C.Dominates D ↔
      ∀ t : Time, SliceDominatesMeasure (C.diracSum t) (D.diracSum t) :=
  Iff.rfl

theorem Cloud.dominates_refl [MeasurableSpace X] [Preorder X]
    (C : Cloud Time Root α X) :
    C.Dominates C :=
  fun _ => sliceDominatesMeasure_refl _

theorem Cloud.dominates_trans [MeasurableSpace X] [Preorder X]
    {C D E : Cloud Time Root α X} (hCD : C.Dominates D) (hDE : D.Dominates E) :
    C.Dominates E :=
  fun t => sliceDominatesMeasure_trans (hCD t) (hDE t)

theorem Cloud.dominatesBy_refl {Position Value : Type*}
    [MeasurableSpace Value] [Preorder Value]
    (φ : Position → Value) (C : Cloud Time Root α Position) :
    C.DominatesBy φ C :=
  Cloud.dominates_refl _

theorem Cloud.dominatesBy_trans {Position Value : Type*}
    [MeasurableSpace Value] [Preorder Value]
    (φ : Position → Value) {C D E : Cloud Time Root α Position}
    (hCD : C.DominatesBy φ D) (hDE : D.DominatesBy φ E) :
    C.DominatesBy φ E :=
  Cloud.dominates_trans hCD hDE

/-- The same order read in the reversed order on the positions, time slice by time
slice. This is the upper-tail form of B\'erard and Gou\'er\'e. -/
theorem Cloud.dominates_orderDual_iff [MeasurableSpace X] [Preorder X]
    (C D : Cloud Time Root α X)
    (hIic : ∀ a : X, MeasurableSet (Set.Iic (OrderDual.toDual a))) :
    (C.mapOrderDual).Dominates (D.mapOrderDual) ↔
      ∀ t (a : X), C.diracSum t (Set.Ici a) ≤ D.diracSum t (Set.Ici a) := by
  constructor
  · intro h t a
    have h' := h t (OrderDual.toDual a)
    rwa [Cloud.mapOrderDual_diracSum_Iic (C := C) t a (hIic a),
      Cloud.mapOrderDual_diracSum_Iic (C := D) t a (hIic a)] at h'
  · intro h t a
    have h' := h t (OrderDual.ofDual a)
    rw [show (Set.Iic a : Set (OrderDual X)) =
      Set.Iic (OrderDual.toDual (OrderDual.ofDual a)) from rfl,
      Cloud.mapOrderDual_diracSum_Iic (C := C) t (OrderDual.ofDual a) (hIic _),
      Cloud.mapOrderDual_diracSum_Iic (C := D) t (OrderDual.ofDual a) (hIic _)]
    exact h'

/-- A slice with no particles carries no mass, so a cloud whose slices are all empty is a
least element of the domination order. -/
theorem Cloud.dominates_of_particles_eq_empty [MeasurableSpace X] [MeasurableSingletonClass X]
    [Preorder X] [Countable (RootIndexed.TreeNode Root α)] {C D : Cloud Time Root α X} (h : ∀ t, C.particles t = ∅) :
    C.Dominates D := by
  rw [Cloud.Dominates]
  intro t
  rw [SliceDominatesMeasure]
  intro a
  have hC : C.diracSum t (Set.Iic a) = 0 := by
    rw [Cloud.diracSum_apply_of_countable C t (Set.Iic a), h t]
    exact tsum_empty
  rw [hC]
  exact zero_le

/-- On countable slices whose ranks separate their particles, the rankwise form of the order at
every time implies domination, which is the order stated on the cloud's Dirac sums. -/
theorem Cloud.dominates_of_rankwiseDominates_of_countable [MeasurableSpace X]
    [MeasurableSingletonClass X] [Countable (RootIndexed.TreeNode Root α)] [LT (RootIndexed.TreeNode Root α)]
    [Preorder X] {C D : Cloud Time Root α X}
    (hinj : ∀ t, Set.InjOn (C.sliceRank t) (C.particles t))
    (h : ∀ t, C.RankwiseDominates D t) : C.Dominates D :=
  fun t => Cloud.rankwiseDominates_diracSum_of_countable t (hinj t) (h t)

/-- Rankwise comparison of the observed positions implies domination through
that observation. -/
theorem Cloud.dominatesBy_of_rankwiseDominatesBy_of_countable
    {Position Value : Type*} [MeasurableSpace Value]
    [MeasurableSingletonClass Value]
    [Countable (RootIndexed.TreeNode Root α)]
    [LT (RootIndexed.TreeNode Root α)] [Preorder Value]
    (φ : Position → Value) {C D : Cloud Time Root α Position}
    (hinj : ∀ t, Set.InjOn ((C.mapPosition φ).sliceRank t) (C.particles t))
    (h : ∀ t, C.RankwiseDominatesBy φ D t) : C.DominatesBy φ D :=
  Cloud.dominates_of_rankwiseDominates_of_countable hinj h

end Branching

end Combinatorics

end

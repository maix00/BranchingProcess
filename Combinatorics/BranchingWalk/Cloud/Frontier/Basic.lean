/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Cloud.Basic
public import Mathlib.Order.Bounds.Basic

/-!
# Deterministic cloud frontiers

## Public declarations

The declarations prefixed with `CloudSet.` are in namespace
`Combinatorics.Branching.CloudSet`; the scalar-observation specializations
prefixed with `Cloud.` are in namespace `Combinatorics.Branching.Cloud`.

- `CloudSet.lowerFrontier`, `CloudSet.upperFrontier`,
  `CloudSet.mem_lowerFrontier_iff`, `CloudSet.lowerFrontier_subset_points`,
  `CloudSet.mem_upperFrontier_iff`, and
  `CloudSet.upperFrontier_subset_points`: the least and greatest points in a
  slice, characterized by `IsLeast` and `IsGreatest` and contained in that
  slice.
- `CloudSet.mem_upperFrontier_iff_orderDual` identifies the upper frontier
  with the lower frontier after reversing the order.
- `CloudSet.unattainedLowerExample`,
  `CloudSet.unattainedLowerExample_points_nonempty`, and
  `CloudSet.unattainedLowerExample_lowerFrontier_empty` give a nonempty real
  slice with no attained lower frontier.
- `CloudSet.potentialValues`, `CloudSet.lowerPotentialFrontier`, and
  `CloudSet.upperPotentialFrontier` give the image of a slice under a real
  potential and its extremal points. `CloudSet.mem_lowerPotentialFrontier_iff`
  and `CloudSet.mem_upperPotentialFrontier_iff` characterize them by
  `IsLeast` and `IsGreatest` in `potentialValues`.
- `CloudSet.HasLowerPotentialPoint`, `CloudSet.lowerPotentialPoint`,
  `CloudSet.lowerPotentialPoint_mem_frontier`, and
  `CloudSet.isLeast_lowerPotentialPoint`: when the lower potential frontier
  is nonempty, choose a point in it that is least among observed values.
- `CloudSet.lowerPotentialFrontier_id` and
  `CloudSet.upperPotentialFrontier_id`: the identity potential recovers the
  ordinary frontiers.
- `Cloud.lowerPotentialFrontier`, `Cloud.upperPotentialFrontier`,
  `Cloud.potentialValues`, `Cloud.HasLowerPotentialPoint`, and
  `Cloud.lowerPotentialPoint` delegate these operations to `C.support`.
- `Cloud.lowerPotentialPoint_mem_frontier` and
  `Cloud.isLeast_lowerPotentialPoint` give the selected point's properties;
  `Cloud.lowerPotentialFrontier_id` and `Cloud.upperPotentialFrontier_id`
  recover the support frontiers for the identity potential.

`lowerFrontier C t` and `upperFrontier C t` are the sets of least and
greatest positions in the time slice `C.points t`. They record all extremal
points when the order has ties. A frontier is empty when its slice has no
attained extremum; `unattainedLowerExample` gives a nonempty slice with empty
lower frontier. The two definitions are order-dual to one another.

The public API is:

- `lowerFrontier C t` and `upperFrontier C t` are the least and greatest
  elements of the slice as sets; their membership theorems characterize
  these sets by `IsLeast` and `IsGreatest`, and the subset theorems place each
  frontier inside the original slice.
- `mem_upperFrontier_iff_orderDual` identifies the upper frontier with the
  lower frontier after reversing the order. `unattainedLowerExample` proves
  that an infinite nonempty slice can have no least point.
- `Cloud.lowerPotentialFrontier`, `upperPotentialFrontier`, and
  `potentialValues` apply a real-valued potential to a particle cloud.
  `HasLowerPotentialPoint` states attainment; `lowerPotentialPoint` chooses
  an attained lower point and the accompanying theorems show it belongs to
  the frontier and is least among the potential values.

The exact frontier laws are `CloudSet.mem_lowerFrontier_iff`,
`CloudSet.lowerFrontier_subset_points`, `CloudSet.mem_upperFrontier_iff`,
`CloudSet.upperFrontier_subset_points`, and
`CloudSet.mem_upperFrontier_iff_orderDual`. In particular, both frontiers are
subsets of `C.points t`, and upper-frontier membership is equivalent to
lower-frontier membership after applying `OrderDual.toDual`. The example laws
`CloudSet.unattainedLowerExample_points_nonempty` and
`CloudSet.unattainedLowerExample_lowerFrontier_empty` give a nonempty slice
with no least point.

For a scalar observation, `Cloud.lowerPotentialPoint_mem_frontier` and
`Cloud.isLeast_lowerPotentialPoint` state that an attained selector lies in
`C.lowerPotentialFrontier potential t` and is least in
`C.potentialValues potential t`. The identity cases are
`Cloud.lowerPotentialFrontier_id` and `Cloud.upperPotentialFrontier_id`.
-/

@[expose] public section

/-! ### Failure of attainment for an infinite slice -/

namespace Combinatorics

namespace Branching

namespace CloudSet

variable {Time X : Type*}

/-- The lower frontier of a cloud at a fixed time: the least points of that
time slice. -/
def lowerFrontier [LE X] (C : CloudSet Time X) (t : Time) : Set X :=
  {x | IsLeast {y | y ∈ C.points t} x}

@[simp] theorem mem_lowerFrontier_iff [LE X] (C : CloudSet Time X) (t : Time)
    (x : X) :
    x ∈ C.lowerFrontier t ↔ IsLeast {y | y ∈ C.points t} x :=
  Iff.rfl

theorem lowerFrontier_subset_points [LE X] (C : CloudSet Time X) (t : Time) :
    C.lowerFrontier t ⊆ C.points t := by
  intro x hx
  exact hx.1

/-- The upper frontier of a cloud at a fixed time: the greatest points of
that time slice. -/
def upperFrontier [LE X] (C : CloudSet Time X) (t : Time) : Set X :=
  {x | IsGreatest {y | y ∈ C.points t} x}

@[simp] theorem mem_upperFrontier_iff [LE X] (C : CloudSet Time X) (t : Time)
    (x : X) :
    x ∈ C.upperFrontier t ↔ IsGreatest {y | y ∈ C.points t} x :=
  Iff.rfl

theorem upperFrontier_subset_points [LE X] (C : CloudSet Time X) (t : Time) :
    C.upperFrontier t ⊆ C.points t := by
  intro x hx
  exact hx.1

/-- The potential values present in one time slice. -/
def potentialValues (C : CloudSet Time X) (potential : X → ℝ) (t : Time) : Set ℝ :=
  potential '' C.points t

/-- The lower frontier of the potential values in one time slice. -/
def lowerPotentialFrontier (C : CloudSet Time X)
    (potential : X → ℝ) (t : Time) : Set ℝ :=
  (C.map potential).lowerFrontier t

/-- The upper frontier of the potential values in one time slice. -/
def upperPotentialFrontier (C : CloudSet Time X)
    (potential : X → ℝ) (t : Time) : Set ℝ :=
  (C.map potential).upperFrontier t

@[simp] theorem mem_lowerPotentialFrontier_iff
    (C : CloudSet Time X) (potential : X → ℝ) (t : Time) (x : ℝ) :
    x ∈ C.lowerPotentialFrontier potential t ↔
      IsLeast (C.potentialValues potential t) x :=
  Iff.rfl

@[simp] theorem mem_upperPotentialFrontier_iff
    (C : CloudSet Time X) (potential : X → ℝ) (t : Time) (x : ℝ) :
    x ∈ C.upperPotentialFrontier potential t ↔
      IsGreatest (C.potentialValues potential t) x :=
  Iff.rfl

/-- Whether the lower edge of the potential values is attained. -/
def HasLowerPotentialPoint (C : CloudSet Time X)
    (potential : X → ℝ) (t : Time) : Prop :=
  (C.lowerPotentialFrontier potential t).Nonempty

/-- Choose an attained lower point of the potential values. -/
noncomputable def lowerPotentialPoint (C : CloudSet Time X)
    (potential : X → ℝ) (t : Time)
    (h : C.HasLowerPotentialPoint potential t) : ℝ :=
  h.choose

theorem lowerPotentialPoint_mem_frontier
    (C : CloudSet Time X) (potential : X → ℝ) (t : Time)
    (h : C.HasLowerPotentialPoint potential t) :
    C.lowerPotentialPoint potential t h ∈ C.lowerPotentialFrontier potential t :=
  h.choose_spec

theorem isLeast_lowerPotentialPoint
    (C : CloudSet Time X) (potential : X → ℝ) (t : Time)
    (h : C.HasLowerPotentialPoint potential t) :
    IsLeast (C.potentialValues potential t)
      (C.lowerPotentialPoint potential t h) :=
  h.choose_spec

@[simp] theorem lowerPotentialFrontier_id (C : CloudSet Time ℝ) (t : Time) :
    C.lowerPotentialFrontier id t = C.lowerFrontier t := by
  ext x
  simp [lowerPotentialFrontier, CloudSet.map, CloudSet.lowerFrontier]

@[simp] theorem upperPotentialFrontier_id (C : CloudSet Time ℝ) (t : Time) :
    C.upperPotentialFrontier id t = C.upperFrontier t := by
  ext x
  simp [upperPotentialFrontier, CloudSet.map, CloudSet.upperFrontier]

/-- The upper frontier is the lower frontier after reversing the order on
values. -/
theorem mem_upperFrontier_iff_orderDual [LE X]
    (C : CloudSet Time X) (t : Time) (x : X) :
    x ∈ C.upperFrontier t ↔
      OrderDual.toDual x ∈ (C.mapOrderDual).lowerFrontier t := by
  simp only [upperFrontier, lowerFrontier, Set.mem_ofPred_eq,
    IsGreatest, IsLeast]
  constructor
  · rintro ⟨hx, hmax⟩
    constructor
    · simpa using hx
    · intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      exact (OrderDual.toDual_le_toDual).2 (hmax hy)
  · rintro ⟨hxdual, hmin⟩
    constructor
    · simpa using hxdual
    · intro y hy
      have hydual : OrderDual.toDual y ∈ (C.mapOrderDual).points t :=
        ⟨y, hy, rfl⟩
      exact (OrderDual.toDual_le_toDual).1 (hmin hydual)

/-- A nonempty cloud slice whose lower infimum is not occupied. -/
def unattainedLowerExample : CloudSet Unit ℝ where
  points _ := Set.Ioi 0

theorem unattainedLowerExample_points_nonempty :
    (unattainedLowerExample.points ()).Nonempty := by
  exact ⟨1, by simp [unattainedLowerExample]⟩

theorem unattainedLowerExample_lowerFrontier_empty :
    unattainedLowerExample.lowerFrontier () = ∅ := by
  ext x
  constructor
  · intro hx
    have hxpos : 0 < x := hx.1
    have hhalf : x / 2 ∈ unattainedLowerExample.points () := by
      simp [unattainedLowerExample]
      linarith
    have hle := hx.2 hhalf
    simp only [Set.mem_empty_iff_false]
    linarith
  · simp

end CloudSet

namespace Cloud

variable {Time Root α Position : Type*}

/-- The scalar lower frontier seen through a real-valued observation of an
otherwise arbitrary position space. -/
def lowerPotentialFrontier (C : Cloud Time Root α Position)
    (potential : Position → ℝ) (t : Time) : Set ℝ :=
  C.support.lowerPotentialFrontier potential t

/-- The scalar upper frontier seen through a real-valued observation. -/
def upperPotentialFrontier (C : Cloud Time Root α Position)
    (potential : Position → ℝ) (t : Time) : Set ℝ :=
  C.support.upperPotentialFrontier potential t

/-- The potential values actually occupied at time `t`. This is the set whose
infimum describes the lower scalar edge even when no particle realizes it. -/
def potentialValues (C : Cloud Time Root α Position)
    (potential : Position → ℝ) (t : Time) : Set ℝ :=
  C.support.potentialValues potential t

/-- Whether the lower scalar edge is attained by an actual particle. For an
infinite cloud this is additional information: a nonempty set of potential
values can have an infimum without a least element. -/
def HasLowerPotentialPoint (C : Cloud Time Root α Position)
    (potential : Position → ℝ) (t : Time) : Prop :=
  C.support.HasLowerPotentialPoint potential t

/-- An attained scalar lower-frontier point. The witness is available only
under the explicit attainment hypothesis; no ordering of particles is used. -/
noncomputable def lowerPotentialPoint (C : Cloud Time Root α Position)
    (potential : Position → ℝ) (t : Time)
    (h : C.HasLowerPotentialPoint potential t) : ℝ :=
  C.support.lowerPotentialPoint potential t h

theorem lowerPotentialPoint_mem_frontier
    (C : Cloud Time Root α Position) (potential : Position → ℝ) (t : Time)
    (h : C.HasLowerPotentialPoint potential t) :
    C.lowerPotentialPoint potential t h ∈ C.lowerPotentialFrontier potential t :=
  C.support.lowerPotentialPoint_mem_frontier potential t h

theorem isLeast_lowerPotentialPoint
    (C : Cloud Time Root α Position) (potential : Position → ℝ) (t : Time)
    (h : C.HasLowerPotentialPoint potential t) :
    IsLeast (C.potentialValues potential t)
      (C.lowerPotentialPoint potential t h) :=
  C.support.isLeast_lowerPotentialPoint potential t h

@[simp] theorem lowerPotentialFrontier_id
    (C : Cloud Time Root α ℝ) (t : Time) :
    C.lowerPotentialFrontier id t = C.support.lowerFrontier t := by
  simp [lowerPotentialFrontier]

@[simp] theorem upperPotentialFrontier_id
    (C : Cloud Time Root α ℝ) (t : Time) :
    C.upperPotentialFrontier id t = C.support.upperFrontier t := by
  simp [upperPotentialFrontier]

end Cloud

end Branching

end Combinatorics

end

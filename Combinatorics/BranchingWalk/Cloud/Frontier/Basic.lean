import Combinatorics.BranchingWalk.Cloud.Basic
import Mathlib.Order.Bounds.Basic

/-!
# Deterministic cloud frontiers

`lowerFrontier C t` and `upperFrontier C t` are the sets of least and
greatest positions in the time slice `C.points t`. They are empty exactly
when the slice is empty, and they record all extremal points when the order
has ties. The two definitions are order-dual to one another.
-/

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

end CloudSet

namespace Cloud

variable {Time Root α Position : Type*}

/-- The scalar lower frontier seen through a real-valued observation of an
otherwise arbitrary position space. -/
def lowerPotentialFrontier (C : Cloud Time Root α Position)
    (potential : Position → ℝ) (t : Time) : Set ℝ :=
  (C.mapPosition potential).support.lowerFrontier t

/-- The scalar upper frontier seen through a real-valued observation. -/
def upperPotentialFrontier (C : Cloud Time Root α Position)
    (potential : Position → ℝ) (t : Time) : Set ℝ :=
  (C.mapPosition potential).support.upperFrontier t

@[simp] theorem lowerPotentialFrontier_id
    (C : Cloud Time Root α ℝ) (t : Time) :
    C.lowerPotentialFrontier id t = C.support.lowerFrontier t := by
  ext x
  simp [lowerPotentialFrontier, Cloud.mapPosition, Cloud.support,
    CloudSet.lowerFrontier]

@[simp] theorem upperPotentialFrontier_id
    (C : Cloud Time Root α ℝ) (t : Time) :
    C.upperPotentialFrontier id t = C.support.upperFrontier t := by
  ext x
  simp [upperPotentialFrontier, Cloud.mapPosition, Cloud.support,
    CloudSet.upperFrontier]

end Cloud

end Branching

end Combinatorics

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Cloud.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.CompleteLattice.Basic

/-!
# Deterministic cloud frontiers

## Public declarations

`CloudSet.lowerFrontier` and `upperFrontier` are $\inf C_t$ and $\sup C_t$
in any complete lattice. `lowerFrontier_eq_of_isLeast` and
`upperFrontier_eq_of_isGreatest` identify attained extrema with those values;
`lowerFrontier_mapOrderDual` exchanges them on reversing the value order.
`Cloud.lowerFrontierBy` and `upperFrontierBy` apply the same infimum/supremum
to an arbitrary key on indexed particles. `lowerFrontierBy_of_empty` and
`upperFrontierBy_of_empty` give top and bottom for an empty population.
`Cloud.lowerFrontierBy_state_eq` and `upperFrontierBy_state_eq` identify
state ordering with these same operations on the geometric cloud.
The `...FrontierPoints` operations below record attainment separately.

The `CloudSet.` declarations are in namespace `Combinatorics.Branching.CloudSet`;
the scalar-observation specializations prefixed with `Cloud.` are in
`Combinatorics.Branching.Cloud`.

- `CloudSet.lowerFrontierPoints C t` and `CloudSet.upperFrontierPoints C t` are the sets
  `\(\{x \mid \operatorname{IsLeast}(C.points\ t,x)\}\)` and
  `\(\{x \mid \operatorname{IsGreatest}(C.points\ t,x)\}\)`. Their
  characterizations are `CloudSet.mem_lowerFrontierPoints_iff` and
  `CloudSet.mem_upperFrontierPoints_iff`; `CloudSet.lowerFrontierPoints_subset_points`
  and `CloudSet.upperFrontierPoints_subset_points` prove both sets are subsets of
  `C.points t`.
- `CloudSet.mem_upperFrontierPoints_iff_orderDual` states
  `\(x \in C.upperFrontierPoints\ t \iff
  \operatorname{toDual}(x) \in (C.mapOrderDual).lowerFrontierPoints\ t\)`.
  `CloudSet.unattainedLowerExample`,
  `CloudSet.unattainedLowerExample_points_nonempty` and
  `CloudSet.unattainedLowerExample_lowerFrontierPoints_empty` exhibit a nonempty
  real slice whose lower frontier is empty.
- `CloudSet.potentialValues C potential t` is
  `\(\operatorname{potential} '' C.points\ t\)`. The lower and upper
  potential frontiers consist of its least and greatest values, respectively;
  `CloudSet.mem_lowerPotentialFrontierPoints_iff` and
  `CloudSet.mem_upperPotentialFrontierPoints_iff` state the corresponding
  `IsLeast` and `IsGreatest` equivalences.
- `CloudSet.HasLowerPotentialPoint C potential t` means the lower potential
  frontier is nonempty. `CloudSet.lowerPotentialPoint` chooses such a value;
  under the attainment hypothesis,
  `CloudSet.lowerPotentialPoint_mem_frontier` and
  `CloudSet.isLeast_lowerPotentialPoint` give
  `\(x \in C.lowerPotentialFrontierPoints\ potential\ t\)` and
  `\(\operatorname{IsLeast}(C.potentialValues\ potential\ t,x)\)` for the
  chosen point `x`.
- `CloudSet.lowerPotentialFrontierPoints_id` and
  `CloudSet.upperPotentialFrontierPoints_id` identify the potential frontiers for
  `id` with the ordinary frontiers. `Cloud.lowerPotentialFrontierPoints`,
  `Cloud.upperPotentialFrontierPoints`, `Cloud.potentialValues`,
  `Cloud.HasLowerPotentialPoint`, and `Cloud.lowerPotentialPoint` transfer
  these definitions from `C.support`; `Cloud.lowerPotentialPoint_mem_frontier`,
  `Cloud.isLeast_lowerPotentialPoint`, `Cloud.lowerPotentialFrontierPoints_id`, and
  `Cloud.upperPotentialFrontierPoints_id` state their corresponding properties for
  a particle cloud.
-/

@[expose] public section

/-! ### Failure of attainment for an infinite slice -/

namespace Combinatorics

namespace Branching

namespace CloudSet

variable {Time X : Type*}

/-- The lower frontier is the infimum, whether or not a particle attains it. -/
def lowerFrontier [CompleteLattice X] (C : CloudSet Time X) (t : Time) : X :=
  sInf (C.points t)

/-- The upper frontier is the supremum, whether or not a particle attains it. -/
def upperFrontier [CompleteLattice X] (C : CloudSet Time X) (t : Time) : X :=
  sSup (C.points t)

/-- An attained least value equals the infimum frontier. -/
theorem lowerFrontier_eq_of_isLeast [CompleteLattice X] (C : CloudSet Time X)
    (t : Time) {x : X} (hx : IsLeast (C.points t) x) : C.lowerFrontier t = x :=
  le_antisymm (sInf_le hx.1) (le_sInf hx.2)

/-- An attained greatest value equals the supremum frontier. -/
theorem upperFrontier_eq_of_isGreatest [CompleteLattice X] (C : CloudSet Time X)
    (t : Time) {x : X} (hx : IsGreatest (C.points t) x) : C.upperFrontier t = x :=
  le_antisymm (sSup_le hx.2) (le_sSup hx.1)

/-- Reversing the value order exchanges infimum and supremum frontiers. -/
theorem lowerFrontier_mapOrderDual [CompleteLattice X] (C : CloudSet Time X) (t : Time) :
    (C.mapOrderDual).lowerFrontier t = OrderDual.toDual (C.upperFrontier t) := by
  simp only [lowerFrontier, upperFrontier, CloudSet.mapOrderDual, toDual_sSup]
  congr 1
  ext x
  simp


/-- The lower frontier of a cloud at a fixed time: the least points of that
time slice. -/
def lowerFrontierPoints [LE X] (C : CloudSet Time X) (t : Time) : Set X :=
  {x | IsLeast {y | y ∈ C.points t} x}

@[simp] theorem mem_lowerFrontierPoints_iff [LE X] (C : CloudSet Time X) (t : Time)
    (x : X) :
    x ∈ C.lowerFrontierPoints t ↔ IsLeast {y | y ∈ C.points t} x :=
  Iff.rfl

theorem lowerFrontierPoints_subset_points [LE X] (C : CloudSet Time X) (t : Time) :
    C.lowerFrontierPoints t ⊆ C.points t := by
  intro x hx
  exact hx.1

/-- The upper frontier of a cloud at a fixed time: the greatest points of
that time slice. -/
def upperFrontierPoints [LE X] (C : CloudSet Time X) (t : Time) : Set X :=
  {x | IsGreatest {y | y ∈ C.points t} x}

@[simp] theorem mem_upperFrontierPoints_iff [LE X] (C : CloudSet Time X) (t : Time)
    (x : X) :
    x ∈ C.upperFrontierPoints t ↔ IsGreatest {y | y ∈ C.points t} x :=
  Iff.rfl

theorem upperFrontierPoints_subset_points [LE X] (C : CloudSet Time X) (t : Time) :
    C.upperFrontierPoints t ⊆ C.points t := by
  intro x hx
  exact hx.1

/-- The potential values present in one time slice. -/
def potentialValues (C : CloudSet Time X) (potential : X → ℝ) (t : Time) : Set ℝ :=
  potential '' C.points t

/-- The lower frontier of the potential values in one time slice. -/
def lowerPotentialFrontierPoints (C : CloudSet Time X)
    (potential : X → ℝ) (t : Time) : Set ℝ :=
  (C.map potential).lowerFrontierPoints t

/-- The upper frontier of the potential values in one time slice. -/
def upperPotentialFrontierPoints (C : CloudSet Time X)
    (potential : X → ℝ) (t : Time) : Set ℝ :=
  (C.map potential).upperFrontierPoints t

@[simp] theorem mem_lowerPotentialFrontierPoints_iff
    (C : CloudSet Time X) (potential : X → ℝ) (t : Time) (x : ℝ) :
    x ∈ C.lowerPotentialFrontierPoints potential t ↔
      IsLeast (C.potentialValues potential t) x :=
  Iff.rfl

@[simp] theorem mem_upperPotentialFrontierPoints_iff
    (C : CloudSet Time X) (potential : X → ℝ) (t : Time) (x : ℝ) :
    x ∈ C.upperPotentialFrontierPoints potential t ↔
      IsGreatest (C.potentialValues potential t) x :=
  Iff.rfl

/-- Whether the lower edge of the potential values is attained. -/
def HasLowerPotentialPoint (C : CloudSet Time X)
    (potential : X → ℝ) (t : Time) : Prop :=
  (C.lowerPotentialFrontierPoints potential t).Nonempty

/-- Choose an attained lower point of the potential values. -/
noncomputable def lowerPotentialPoint (C : CloudSet Time X)
    (potential : X → ℝ) (t : Time)
    (h : C.HasLowerPotentialPoint potential t) : ℝ :=
  h.choose

theorem lowerPotentialPoint_mem_frontier
    (C : CloudSet Time X) (potential : X → ℝ) (t : Time)
    (h : C.HasLowerPotentialPoint potential t) :
    C.lowerPotentialPoint potential t h ∈ C.lowerPotentialFrontierPoints potential t :=
  h.choose_spec

theorem isLeast_lowerPotentialPoint
    (C : CloudSet Time X) (potential : X → ℝ) (t : Time)
    (h : C.HasLowerPotentialPoint potential t) :
    IsLeast (C.potentialValues potential t)
      (C.lowerPotentialPoint potential t h) :=
  h.choose_spec

@[simp] theorem lowerPotentialFrontierPoints_id (C : CloudSet Time ℝ) (t : Time) :
    C.lowerPotentialFrontierPoints id t = C.lowerFrontierPoints t := by
  ext x
  simp [lowerPotentialFrontierPoints, CloudSet.map, CloudSet.lowerFrontierPoints]

@[simp] theorem upperPotentialFrontierPoints_id (C : CloudSet Time ℝ) (t : Time) :
    C.upperPotentialFrontierPoints id t = C.upperFrontierPoints t := by
  ext x
  simp [upperPotentialFrontierPoints, CloudSet.map, CloudSet.upperFrontierPoints]

/-- The upper frontier is the lower frontier after reversing the order on
values. -/
theorem mem_upperFrontierPoints_iff_orderDual [LE X]
    (C : CloudSet Time X) (t : Time) (x : X) :
    x ∈ C.upperFrontierPoints t ↔
      OrderDual.toDual x ∈ (C.mapOrderDual).lowerFrontierPoints t := by
  simp only [upperFrontierPoints, lowerFrontierPoints, Set.mem_ofPred_eq,
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

theorem unattainedLowerExample_lowerFrontierPoints_empty :
    unattainedLowerExample.lowerFrontierPoints () = ∅ := by
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

/-- Infimum of any ordering key on the indexed population, including empty populations. -/
def lowerFrontierBy {K : Type*} [CompleteLattice K]
    (C : Cloud Time Root α Position) (key : Combinatorics.UlamHarris.RootIndexed.TreeNode Root α → K)
    (t : Time) : K :=
  sInf (key '' C.particles t)

/-- Supremum of any ordering key on the indexed population. -/
def upperFrontierBy {K : Type*} [CompleteLattice K]
    (C : Cloud Time Root α Position) (key : Combinatorics.UlamHarris.RootIndexed.TreeNode Root α → K)
    (t : Time) : K :=
  sSup (key '' C.particles t)

/-- State-dependent ordering is a special case of a key on indexed particles. -/
theorem lowerFrontierBy_state_eq {K : Type*} [CompleteLattice K]
    (C : Cloud Time Root α Position) (φ : Position → K) (t : Time) :
    C.lowerFrontierBy (fun q ↦ φ (C.position q.1 q.2)) t =
      (C.support.map φ).lowerFrontier t := by
  simp [lowerFrontierBy, CloudSet.lowerFrontier, Cloud.support, CloudSet.map, Set.image_image]

/-- The analogous state-dependent upper frontier is a supremum. -/
theorem upperFrontierBy_state_eq {K : Type*} [CompleteLattice K]
    (C : Cloud Time Root α Position) (φ : Position → K) (t : Time) :
    C.upperFrontierBy (fun q ↦ φ (C.position q.1 q.2)) t =
      (C.support.map φ).upperFrontier t := by
  simp [upperFrontierBy, CloudSet.upperFrontier, Cloud.support, CloudSet.map, Set.image_image]

/-- Empty populations have lower frontier top. -/
theorem lowerFrontierBy_of_empty {K : Type*} [CompleteLattice K]
    (C : Cloud Time Root α Position) (key : Combinatorics.UlamHarris.RootIndexed.TreeNode Root α → K)
    (t : Time) (h : C.particles t = ∅) : C.lowerFrontierBy key t = ⊤ := by
  simp [lowerFrontierBy, h]

/-- Empty populations have upper frontier bottom. -/
theorem upperFrontierBy_of_empty {K : Type*} [CompleteLattice K]
    (C : Cloud Time Root α Position) (key : Combinatorics.UlamHarris.RootIndexed.TreeNode Root α → K)
    (t : Time) (h : C.particles t = ∅) : C.upperFrontierBy key t = ⊥ := by
  simp [upperFrontierBy, h]


/-- The scalar lower frontier seen through a real-valued observation of an
otherwise arbitrary position space. -/
def lowerPotentialFrontierPoints (C : Cloud Time Root α Position)
    (potential : Position → ℝ) (t : Time) : Set ℝ :=
  C.support.lowerPotentialFrontierPoints potential t

/-- The scalar upper frontier seen through a real-valued observation. -/
def upperPotentialFrontierPoints (C : Cloud Time Root α Position)
    (potential : Position → ℝ) (t : Time) : Set ℝ :=
  C.support.upperPotentialFrontierPoints potential t

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
    C.lowerPotentialPoint potential t h ∈ C.lowerPotentialFrontierPoints potential t :=
  C.support.lowerPotentialPoint_mem_frontier potential t h

theorem isLeast_lowerPotentialPoint
    (C : Cloud Time Root α Position) (potential : Position → ℝ) (t : Time)
    (h : C.HasLowerPotentialPoint potential t) :
    IsLeast (C.potentialValues potential t)
      (C.lowerPotentialPoint potential t h) :=
  C.support.isLeast_lowerPotentialPoint potential t h

@[simp] theorem lowerPotentialFrontierPoints_id
    (C : Cloud Time Root α ℝ) (t : Time) :
    C.lowerPotentialFrontierPoints id t = C.support.lowerFrontierPoints t := by
  simp [lowerPotentialFrontierPoints]

@[simp] theorem upperPotentialFrontierPoints_id
    (C : Cloud Time Root α ℝ) (t : Time) :
    C.upperPotentialFrontierPoints id t = C.support.upperFrontierPoints t := by
  simp [upperPotentialFrontierPoints]

end Cloud

end Branching

end Combinatorics

end

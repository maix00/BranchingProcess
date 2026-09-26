import Combinatorics.BranchingWalk.Cloud.Basic
import Combinatorics.BranchingWalk.Cloud.Order.Slice

/-!
# Domination order on a cloud

A `Cloud Time X` is a family of spatial point sets indexed by time, so the
thesis's order `≽` on populations lifts to clouds by applying the time-slice
relation of `Cloud/Order/Slice.lean` at every time. The result is the relation
that the coupling of `contents/n-brw/killed-coupling.tex` maintains from
generation to generation: the killed process stays to the right of the
`N`-branching random walk at every generation before `τ`.

As at the level of a single slice, there is one definition. The other
direction is the same definition read in the reversed order on the positions,
which `dominates_orderDual_iff` displays in the upper-tail form of B\'erard and
Gou\'er\'e. It is not `Dominates` with the two clouds exchanged, because both
directions keep the same particle-count comparison.

The lift is reflexive and transitive, is monotone when the dominating cloud is
moved left or the dominated cloud is moved right, and inherits the leftmost
comparison `Dominates.isLeast_le`, which is the form used to deduce
`𝓜^N_k ≤ 𝓜^k_k` from the abstract order statement.
-/

namespace Combinatorics

namespace Branching

namespace Cloud

variable {Time X : Type*}

/-- `C` dominates `D` when it dominates `D` in every time slice. -/
def Dominates [Preorder X] (C D : Cloud Time X) : Prop :=
  ∀ t : Time, SliceDominates (C.points t) (D.points t)

theorem dominates_iff [Preorder X] (C D : Cloud Time X) :
    C.Dominates D ↔ ∀ t : Time, SliceDominates (C.points t) (D.points t) :=
  Iff.rfl

theorem dominates_refl [Preorder X] (C : Cloud Time X) :
    C.Dominates C :=
  fun _ => sliceDominates_refl _

theorem dominates_trans [Preorder X] {C D E : Cloud Time X}
    (hCD : C.Dominates D) (hDE : D.Dominates E) :
    C.Dominates E :=
  fun t => sliceDominates_trans (hCD t) (hDE t)

/-- The empty cloud, with no point at any time, dominates every cloud. -/
theorem dominates_emptyCloud [Preorder X] (D : Cloud Time X) :
    ({ points := fun _ : Time => (∅ : Set X) } : Cloud Time X).Dominates D :=
  fun _ => sliceDominates_empty _

/-- Enlarging the dominated cloud and shrinking the dominating one preserves
domination, time slice by time slice. -/
theorem Dominates.mono [Preorder X] {C D C' D' : Cloud Time X}
    (h : C.Dominates D)
    (hC : ∀ t : Time, C'.points t ⊆ C.points t)
    (hD : ∀ t : Time, D.points t ⊆ D'.points t) :
    C'.Dominates D' :=
  fun t => (h t).mono (hC t) (hD t)

/-- The same order read in the reversed order on the positions, time slice by
time slice. This is the cloud-level instance of
`sliceDominates_orderDual_iff`. -/
theorem dominates_orderDual_iff [Preorder X] (C D : Cloud Time X) :
    ({ points := fun t => (C.points t : Set (OrderDual X)) } :
        Cloud Time (OrderDual X)).Dominates
      ({ points := fun t => (D.points t : Set (OrderDual X)) } :
        Cloud Time (OrderDual X)) ↔
      ∀ t x, (C.points t ∩ Set.Ici x).encard ≤
        (D.points t ∩ Set.Ici x).encard := by
  refine forall_congr' fun t => ?_
  exact sliceDominates_orderDual_iff (C.points t) (D.points t)

/-- At any time where both clouds have a leftmost point, the leftmost point of
the dominating cloud lies weakly to the right of the leftmost point of the
dominated one. This is the slicewise form of the thesis's conclusion
`𝓜^N_k ≤ 𝓜^k_k`. -/
theorem Dominates.isLeast_le [LinearOrder X] {C D : Cloud Time X}
    (h : C.Dominates D) {t : Time} {x y : X}
    (hx : IsLeast (C.points t) x) (hy : IsLeast (D.points t) y) :
    y ≤ x :=
  (h t).isLeast_le hx hy

/-- The reversed direction's position comparison: at any time where both
clouds have a rightmost point, the rightmost point of the leftward one lies
weakly to the left of the rightmost point of the other. -/
theorem Dominates.isGreatest_le_orderDual [LinearOrder X] {C D : Cloud Time X}
    (h : ({ points := fun t => (C.points t : Set (OrderDual X)) } :
        Cloud Time (OrderDual X)).Dominates
      ({ points := fun t => (D.points t : Set (OrderDual X)) } :
        Cloud Time (OrderDual X)))
    {t : Time} {x y : X}
    (hx : IsGreatest (C.points t) x) (hy : IsGreatest (D.points t) y) :
    x ≤ y :=
  encard_Ici_isGreatest_le ((dominates_orderDual_iff C D).mp h t) hx hy

end Cloud

end Branching

end Combinatorics

import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Defs

/-!
# Domination order on a single time slice

A population at a fixed time is a finite set of positions on the line, and the
thesis compares two of them by the stochastic order of B\'erard and Gou\'er\'e
(`Brunet-Derrida behavior of branching-selection particle systems on the
line`, arXiv:0811.2782, Section 2). The two directions are the *same*
construction read in the two orders of the line, so this module defines one
relation and recovers the second direction by reversing the order rather than
by repeating the definition.

`SliceDominates A B` counts how much of `A` and of `B` lies weakly below each
threshold, and asks `A` to have no more there. Reversing the order on the line
turns "below" into "above", and the counting form of the reversed relation is
B\'erard and Gou\'er\'e's

`μ([x,+∞[) ≤ ν([x,+∞[)` for every `x`,

which is equivalent to `M(μ) ≤ M(ν)` together with the pointwise comparison of
the two populations listed from the right. That equivalence is
`sliceDominates_orderDual_iff`.

Both directions keep the same particle-count comparison `M(A) ≤ M(B)`; only
the half-line that is counted, and with it the position comparison, is
reversed. Consequently the second direction is *not* `SliceDominates B A`:
the two differ exactly when the two populations have different sizes, which is
why the coupling of `contents/n-brw/killed-coupling.tex` may compare a killed
population with an `N`-population but the lower-bound construction of
`contents/main-results/speed/proof.tex` must place `𝓥^{N|a}` first.

The half-lines are closed (`Set.Iic`, `Set.Ici`), so a least point of `A` is
itself counted at the threshold it defines. This makes the position halves
`SliceDominates.isLeast_le` and `SliceDominates.isGreatest_le_orderDual`
immediate.
-/

namespace MeasureTheory

namespace BranchingWalk

variable {X : Type*}

/-- `A` dominates `B` from the right: at every threshold `A` has at most as
many points weakly below it as `B` does. -/
def SliceDominates [Preorder X] (A B : Set X) : Prop :=
  ∀ t : X, (A ∩ Set.Iic t).encard ≤ (B ∩ Set.Iic t).encard

theorem sliceDominates_refl [Preorder X] (A : Set X) :
    SliceDominates A A :=
  fun _ => le_rfl

theorem sliceDominates_trans [Preorder X] {A B C : Set X}
    (hAB : SliceDominates A B) (hBC : SliceDominates B C) :
    SliceDominates A C :=
  fun t => le_trans (hAB t) (hBC t)

/-- The empty population dominates every population: it has no points, so the
counting inequality is immediate. This is the degenerate case `M(μ) = 0` of
the thesis. -/
theorem sliceDominates_empty [Preorder X] (B : Set X) :
    SliceDominates ∅ B := by
  intro t
  simp

/-- Moving the dominating population left and the dominated population right
preserves domination. This is the "no more points, shifted to the right"
monotonicity used by the coupling induction. -/
theorem SliceDominates.mono [Preorder X] {A B A' B' : Set X}
    (h : SliceDominates A B) (hA : A' ⊆ A) (hB : B ⊆ B') :
    SliceDominates A' B' :=
  fun t => le_trans
    (Set.encard_mono (Set.inter_subset_inter_left _ hA))
    (le_trans (h t) (Set.encard_mono (Set.inter_subset_inter_left _ hB)))

/-- The same relation read in the reversed order is B\'erard and Gou\'er\'e's
upper-tail form: the leftward instance counts how much of each population lies
weakly above each threshold. Reversing the order keeps the arguments in place
and keeps the particle-count comparison, so this is an instance of one
definition rather than a second definition. -/
theorem sliceDominates_orderDual_iff [Preorder X] (A B : Set X) :
    SliceDominates (X := OrderDual X) A B ↔
      ∀ x : X, (A ∩ Set.Ici x).encard ≤ (B ∩ Set.Ici x).encard := by
  have h : ∀ t : X, Set.Iic (α := OrderDual X) t = Set.Ici (α := X) t := by
    intro t
    ext y
    exact OrderDual.toDual_le_toDual
  constructor
  · intro hd x
    have hx := hd x
    rwa [h x] at hx
  · intro hu t
    rw [h t]
    exact hu t

/-- The "no more points" half of the thesis's definition: if both populations
lie weakly below a common threshold, the counting form bounds the size of `A`
by the size of `B`. -/
theorem SliceDominates.encard_le [Preorder X] {A B : Set X}
    (h : SliceDominates A B) {t : X}
    (hA : A ⊆ Set.Iic t) (hB : B ⊆ Set.Iic t) :
    A.encard ≤ B.encard := by
  have hA' : A ∩ Set.Iic t = A := Set.inter_eq_left.mpr hA
  have hB' : B ∩ Set.Iic t = B := Set.inter_eq_left.mpr hB
  simpa [hA', hB'] using h t

/-- The position half of the thesis's definition: if both populations have a
leftmost point, the leftmost point of the dominating population is weakly to
the right of the leftmost point of the dominated one. -/
theorem SliceDominates.isLeast_le [LinearOrder X] {A B : Set X}
    (h : SliceDominates A B) {a b : X} (ha : IsLeast A a) (hb : IsLeast B b) :
    b ≤ a := by
  by_contra hnot
  have hlt : a < b := lt_of_not_ge hnot
  have hA : (A ∩ Set.Iic a).Nonempty := ⟨a, ha.1, le_rfl⟩
  have hB : B ∩ Set.Iic a = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hyB, hya⟩
    exact absurd (le_trans (hb.2 hyB) hya) (not_le_of_gt hlt)
  have hone : (1 : ℕ∞) ≤ (A ∩ Set.Iic a).encard :=
    Set.one_le_encard_iff_nonempty.mpr hA
  have hzero : (A ∩ Set.Iic a).encard ≤ (0 : ℕ∞) := by
    have h' := h a
    rw [hB] at h'
    simpa using h'
  exact absurd (le_trans hone hzero) (by simp)

/-- The position half of the reversed direction, stated in the upper-tail form
of B\'erard and Gou\'er\'e: if both populations have a rightmost point, the
rightmost point of the leftward population is weakly to the left of the
rightmost point of the other one. -/
theorem encard_Ici_isGreatest_le [LinearOrder X] {A B : Set X}
    (h : ∀ x : X, (A ∩ Set.Ici x).encard ≤ (B ∩ Set.Ici x).encard)
    {a b : X} (ha : IsGreatest A a) (hb : IsGreatest B b) :
    a ≤ b := by
  by_contra hnot
  have hlt : b < a := lt_of_not_ge hnot
  have hA : (A ∩ Set.Ici a).Nonempty := ⟨a, ha.1, le_rfl⟩
  have hB : B ∩ Set.Ici a = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hyB, hya⟩
    exact absurd (le_trans hya (hb.2 hyB)) (not_le_of_gt hlt)
  have hone : (1 : ℕ∞) ≤ (A ∩ Set.Ici a).encard :=
    Set.one_le_encard_iff_nonempty.mpr hA
  have hzero : (A ∩ Set.Ici a).encard ≤ (0 : ℕ∞) := by
    have ha' := h a
    rw [hB] at ha'
    simpa using ha'
  exact absurd (le_trans hone hzero) (by simp)

/-- The order-dual instance of `encard_Ici_isGreatest_le`, phrased as a
statement about `SliceDominates` in the reversed order. -/
theorem SliceDominates.isGreatest_le_orderDual [LinearOrder X] {A B : Set X}
    (h : SliceDominates (X := OrderDual X) A B)
    {a b : X} (ha : IsGreatest A a) (hb : IsGreatest B b) :
    a ≤ b :=
  encard_Ici_isGreatest_le ((sliceDominates_orderDual_iff A B).mp h) ha hb

end BranchingWalk

end MeasureTheory

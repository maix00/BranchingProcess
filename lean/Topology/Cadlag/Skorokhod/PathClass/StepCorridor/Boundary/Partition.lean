/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Boundary
public import Mathlib.Data.Finset.Sort

/-!
# The common time partition of two step boundaries

For a corridor with two finite step boundaries, its deterministic partition
is the union of their jump times together with the time endpoints. The
successor of a partition point is the least later point in this finite set.
This gives the exact open time cells on which both boundary values are
constant, including when either boundary has a jump at time one.
-/

open Skorokhod.PathClass.StepCorridor

@[expose] public section

namespace Skorokhod.PathClass.StepCorridor

namespace StepBoundary

/-- The common finite partition points of two step boundaries, including the
endpoints of the time interval. -/
noncomputable def commonKnots (upper lower : StepBoundary) : Finset unitInterval :=
  insert ⊥ (insert ⊤ (upper.knots ∪ lower.knots))

@[simp]
theorem bot_mem_commonKnots (upper lower : StepBoundary) :
    (⊥ : unitInterval) ∈ commonKnots upper lower := by
  simp [commonKnots]

@[simp]
theorem top_mem_commonKnots (upper lower : StepBoundary) :
    (⊤ : unitInterval) ∈ commonKnots upper lower := by
  simp [commonKnots]

/-- The union of the two knot sets is nonempty because it contains the left
endpoint. -/
theorem commonKnots_nonempty (upper lower : StepBoundary) :
    (commonKnots upper lower).Nonempty :=
  ⟨⊥, bot_mem_commonKnots upper lower⟩

/-- Enumerate the common knots in increasing order, then extend the finite
grid constantly after its last point. This definition is deterministic and
does not depend on a process law. -/
noncomputable def commonPartitionGrid (upper lower : StepBoundary) : ℕ → unitInterval :=
  fun k => (commonKnots upper lower).orderEmbOfFin rfl
    ⟨min k ((commonKnots upper lower).card - 1), by
      have hcard := Nat.sub_add_cancel
        (Finset.card_pos.mpr (commonKnots_nonempty upper lower))
      omega⟩

theorem monotone_commonPartitionGrid (upper lower : StepBoundary) :
    Monotone (commonPartitionGrid upper lower) := by
  intro i j hij
  apply (commonKnots upper lower).orderEmbOfFin rfl |>.monotone
  apply Fin.mk_le_mk.mpr
  have hcard := Nat.sub_add_cancel
    (Finset.card_pos.mpr (commonKnots_nonempty upper lower))
  omega

/-- Consecutive entries in the finite common-knot grid are distinct. -/
theorem commonPartitionGrid_strictSucc (upper lower : StepBoundary)
    (k : ℕ) (hk : k < (commonKnots upper lower).card - 1) :
    commonPartitionGrid upper lower k < commonPartitionGrid upper lower (k + 1) := by
  let knots := commonKnots upper lower
  have hk : k < knots.card - 1 := by simpa [knots] using hk
  have hcard : knots.card - 1 + 1 = knots.card :=
    Nat.sub_add_cancel (Finset.card_pos.mpr (commonKnots_nonempty upper lower))
  have hk₁ : k ≤ knots.card - 1 := Nat.le_of_lt hk
  have hk₂ : k + 1 ≤ knots.card - 1 := by omega
  unfold commonPartitionGrid
  apply (knots.orderEmbOfFin rfl).strictMono
  change min k (knots.card - 1) < min (k + 1) (knots.card - 1)
  rw [Nat.min_eq_left hk₁, Nat.min_eq_left hk₂]
  exact Nat.lt_succ_self k

/-- Interpolate linearly between consecutive common knots. The coordinate is
an ordinary real unit-interval point; countable rational observations are
introduced by the probability adapter. -/
noncomputable def commonPartitionCellTime (upper lower : StepBoundary)
    (k : ℕ) (q : unitInterval) : unitInterval := by
  let a : ℝ := commonPartitionGrid upper lower k
  let b : ℝ := commonPartitionGrid upper lower (k + 1)
  let r : ℝ := q
  have hab : a ≤ b := by
    exact_mod_cast monotone_commonPartitionGrid upper lower (Nat.le_succ k)
  have hr0 : 0 ≤ r := q.property.1
  have hr1 : r ≤ 1 := q.property.2
  have ha0 : 0 ≤ a := (commonPartitionGrid upper lower k).property.1
  have ha1 : a ≤ 1 := (commonPartitionGrid upper lower k).property.2
  have hb0 : 0 ≤ b := (commonPartitionGrid upper lower (k + 1)).property.1
  have hb1 : b ≤ 1 := (commonPartitionGrid upper lower (k + 1)).property.2
  refine ⟨a + r * (b - a), ?_⟩
  constructor
  · have hprod : 0 ≤ r * (b - a) := mul_nonneg hr0 (sub_nonneg.mpr hab)
    linarith
  · have hleft : 0 ≤ (1 - r) * (1 - a) :=
      mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr ha1)
    have hright : 0 ≤ r * (1 - b) :=
      mul_nonneg hr0 (sub_nonneg.mpr hb1)
    nlinarith

/-- Cell interpolation is monotone in its unit-interval coordinate. -/
theorem monotone_commonPartitionCellTime (upper lower : StepBoundary) (k : ℕ) :
    Monotone (commonPartitionCellTime upper lower k) := by
  intro q r hqr
  apply Subtype.mk_le_mk.mpr
  change (commonPartitionCellTime upper lower k q : ℝ) ≤
    (commonPartitionCellTime upper lower k r : ℝ)
  dsimp [commonPartitionCellTime]
  let a : ℝ := commonPartitionGrid upper lower k
  let b : ℝ := commonPartitionGrid upper lower (k + 1)
  let q' : ℝ := q
  let r' : ℝ := r
  have hab : a ≤ b := by
    exact_mod_cast monotone_commonPartitionGrid upper lower (Nat.le_succ k)
  have hqr' : q' ≤ r' := hqr
  change a + q' * (b - a) ≤ a + r' * (b - a)
  nlinarith [mul_le_mul_of_nonneg_right hqr' (sub_nonneg.mpr hab)]

/-- The real coordinate of the affine cell interpolation. -/
theorem coe_commonPartitionCellTime (upper lower : StepBoundary)
    (k : ℕ) (q : unitInterval) :
    (commonPartitionCellTime upper lower k q : ℝ) =
      (commonPartitionGrid upper lower k : ℝ) +
        (q : ℝ) * ((commonPartitionGrid upper lower (k + 1) : ℝ) -
          (commonPartitionGrid upper lower k : ℝ)) := rfl

theorem commonPartitionCellTime_left_le (upper lower : StepBoundary)
    (k : ℕ) (q : unitInterval) :
    commonPartitionGrid upper lower k ≤ commonPartitionCellTime upper lower k q := by
  apply Subtype.mk_le_mk.mpr
  change (commonPartitionGrid upper lower k : ℝ) ≤
    (commonPartitionCellTime upper lower k q : ℝ)
  dsimp [commonPartitionCellTime]
  let a : ℝ := commonPartitionGrid upper lower k
  let b : ℝ := commonPartitionGrid upper lower (k + 1)
  let r : ℝ := q
  have hab : a ≤ b := by
    exact_mod_cast monotone_commonPartitionGrid upper lower (Nat.le_succ k)
  have hr0 : 0 ≤ r := q.property.1
  have hprod : 0 ≤ r * (b - a) := mul_nonneg hr0 (sub_nonneg.mpr hab)
  linarith

theorem commonPartitionCellTime_le_right (upper lower : StepBoundary)
    (k : ℕ) (q : unitInterval) :
    commonPartitionCellTime upper lower k q ≤
      commonPartitionGrid upper lower (k + 1) := by
  apply Subtype.mk_le_mk.mpr
  change (commonPartitionCellTime upper lower k q : ℝ) ≤
    (commonPartitionGrid upper lower (k + 1) : ℝ)
  dsimp [commonPartitionCellTime]
  let a : ℝ := commonPartitionGrid upper lower k
  let b : ℝ := commonPartitionGrid upper lower (k + 1)
  let r : ℝ := q
  have hab : a ≤ b := by
    exact_mod_cast monotone_commonPartitionGrid upper lower (Nat.le_succ k)
  have hr1 : r ≤ 1 := q.property.2
  have hprod : 0 ≤ (1 - r) * (b - a) :=
    mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hab)
  nlinarith

/-- Affine interpolation parametrizes the entire closed interval between
consecutive common knots. -/
theorem exists_commonPartitionCellTime_eq
    (upper lower : StepBoundary)
    (i : Fin ((commonKnots upper lower).card - 1))
    {t : unitInterval}
    (hleft : commonPartitionGrid upper lower i.val ≤ t)
    (hright : t ≤ commonPartitionGrid upper lower (i.val + 1)) :
    ∃ q : unitInterval, commonPartitionCellTime upper lower i.val q = t := by
  let left : ℝ := commonPartitionGrid upper lower i.val
  let right : ℝ := commonPartitionGrid upper lower (i.val + 1)
  let target : ℝ := t
  have hlength : 0 < right - left := by
    dsimp [left, right]
    apply sub_pos.mpr
    exact_mod_cast commonPartitionGrid_strictSucc upper lower i.val i.isLt
  have hleft' : left ≤ target := hleft
  have hright' : target ≤ right := hright
  let qvalue : ℝ := (target - left) / (right - left)
  have hq0 : 0 ≤ qvalue := by
    dsimp [qvalue]
    exact div_nonneg (by linarith) hlength.le
  have hq1 : qvalue ≤ 1 := by
    dsimp [qvalue]
    rw [div_le_iff₀ hlength]
    linarith
  let q : unitInterval := ⟨qvalue, hq0, hq1⟩
  refine ⟨q, ?_⟩
  apply Subtype.ext
  change left + (q : ℝ) * (right - left) = target
  dsimp [q, qvalue]
  field_simp [ne_of_gt hlength]
  ring

/-- A coordinate strictly before the right endpoint maps strictly inside a
nondegenerate common-knot cell. -/
theorem commonPartitionCellTime_lt_right (upper lower : StepBoundary)
    (k : ℕ) (hk : k < (commonKnots upper lower).card - 1)
    (q : unitInterval) (hq : q < ⊤) :
    commonPartitionCellTime upper lower k q <
      commonPartitionGrid upper lower (k + 1) := by
  apply Subtype.mk_lt_mk.mpr
  change (commonPartitionCellTime upper lower k q : ℝ) <
    (commonPartitionGrid upper lower (k + 1) : ℝ)
  dsimp [commonPartitionCellTime]
  let a : ℝ := commonPartitionGrid upper lower k
  let b : ℝ := commonPartitionGrid upper lower (k + 1)
  let r : ℝ := q
  have hab : a < b := by
    exact_mod_cast commonPartitionGrid_strictSucc upper lower k hk
  have hr1 : r < 1 := by
    dsimp [r]
    change (q : ℝ) < 1 at hq
    exact hq
  have hprod : 0 < (1 - r) * (b - a) :=
    mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hab)
  nlinarith

@[simp]
theorem commonPartitionCellTime_bot (upper lower : StepBoundary) (k : ℕ) :
    commonPartitionCellTime upper lower k ⊥ =
      commonPartitionGrid upper lower k := by
  apply Subtype.ext
  simp [commonPartitionCellTime]

@[simp]
theorem commonPartitionCellTime_top (upper lower : StepBoundary) (k : ℕ) :
    commonPartitionCellTime upper lower k ⊤ =
      commonPartitionGrid upper lower (k + 1) := by
  apply Subtype.ext
  simp [commonPartitionCellTime]

/-- Before the terminal point, an indexed grid point is the corresponding
entry of the increasing enumeration of the common knot set. -/
theorem commonPartitionGrid_eq_orderEmb (upper lower : StepBoundary)
    (k : ℕ) (hk : k < (commonKnots upper lower).card - 1) :
    commonPartitionGrid upper lower k =
      (commonKnots upper lower).orderEmbOfFin rfl ⟨k, by
        have hcard := Nat.sub_add_cancel
          (Finset.card_pos.mpr (commonKnots_nonempty upper lower))
        omega⟩ := by
  have hk' : k ≤ (commonKnots upper lower).card - 1 := Nat.le_of_lt hk
  simp [commonPartitionGrid, Nat.min_eq_left hk']

/-- The first common partition point is the left endpoint. -/
theorem commonPartitionGrid_zero (upper lower : StepBoundary) :
    commonPartitionGrid upper lower 0 = ⊥ := by
  let knots := commonKnots upper lower
  have hcard : 0 < knots.card := Finset.card_pos.mpr (commonKnots_nonempty upper lower)
  have hmin : knots.min' (Finset.card_pos.mp hcard) = ⊥ := by
    apply le_antisymm
    · exact Finset.min'_le _ _ (bot_mem_commonKnots upper lower)
    · exact bot_le
  have hgrid : commonPartitionGrid upper lower 0 =
      knots.orderEmbOfFin (by simp [knots]) ⟨0, hcard⟩ := by
    simp [commonPartitionGrid, knots]
  rw [hgrid, Finset.orderEmbOfFin_zero (by simp [knots]) hcard, hmin]

/-- The last common partition point is the right endpoint. -/
theorem commonPartitionGrid_last (upper lower : StepBoundary) :
    commonPartitionGrid upper lower
      ((commonKnots upper lower).card - 1) = ⊤ := by
  let knots := commonKnots upper lower
  have hcard : 0 < knots.card := Finset.card_pos.mpr (commonKnots_nonempty upper lower)
  have hmax : knots.max' (Finset.card_pos.mp hcard) = ⊤ := by
    apply le_antisymm
    · exact Finset.max'_le knots (Finset.card_pos.mp hcard) ⊤
        (fun _ _ => le_top)
    · exact Finset.le_max' knots ⊤ (top_mem_commonKnots upper lower)
  have hgrid : commonPartitionGrid upper lower (knots.card - 1) =
      knots.orderEmbOfFin (by simp [knots])
        ⟨knots.card - 1, Nat.sub_lt hcard (Nat.succ_pos 0)⟩ := by
    simp [commonPartitionGrid, knots]
  rw [hgrid, Finset.orderEmbOfFin_last (by simp [knots]) hcard, hmax]

/-- Every common partition knot occurs at its unique finite grid index. -/
theorem exists_fin_commonPartitionGrid_eq
    (upper lower : StepBoundary) {t : unitInterval}
    (ht : t ∈ commonKnots upper lower) :
    ∃ i : Fin (commonKnots upper lower).card,
      commonPartitionGrid upper lower i.val = t := by
  let knots := commonKnots upper lower
  let e := knots.orderEmbOfFin rfl
  let i : Fin knots.card := (knots.orderIsoOfFin rfl).symm ⟨t, ht⟩
  have hle : i.val ≤ knots.card - 1 := by
    have hcard := Nat.sub_add_cancel (Finset.card_pos.mpr (commonKnots_nonempty upper lower))
    omega
  have hgrid : commonPartitionGrid upper lower i.val = e i := by
    change e ⟨min i.val (knots.card - 1), _⟩ = e i
    have hindex : (⟨min i.val (knots.card - 1), by
        have hcard' := Nat.sub_add_cancel
          (Finset.card_pos.mpr (commonKnots_nonempty upper lower))
        omega⟩ : Fin knots.card) = i := by
      apply Fin.ext
      simp [Nat.min_eq_left hle]
    exact congrArg e hindex
  refine ⟨i, ?_⟩
  calc
    commonPartitionGrid upper lower i.val = e i := hgrid
    _ = t := by simp [i, e, knots, Finset.orderEmbOfFin]

/-- The next indexed grid point is the next entry of the increasing
enumeration, when the current index is not terminal. -/
theorem commonPartitionGrid_succ_eq_orderEmb (upper lower : StepBoundary)
    (k : ℕ) (hk : k < (commonKnots upper lower).card - 1) :
    commonPartitionGrid upper lower (k + 1) =
      (commonKnots upper lower).orderEmbOfFin rfl ⟨k + 1, by
        have hcard := Nat.sub_add_cancel
          (Finset.card_pos.mpr (commonKnots_nonempty upper lower))
        omega⟩ := by
  have hcard := Nat.sub_add_cancel
    (Finset.card_pos.mpr (commonKnots_nonempty upper lower))
  have hk' : k + 1 ≤ (commonKnots upper lower).card - 1 := by omega
  simp [commonPartitionGrid, Nat.min_eq_left hk']

/-- Every common knot to the right of an indexed partition point is at or
after its successor in the finite sorted enumeration. -/
theorem commonPartitionGrid_succ_le_of_mem (upper lower : StepBoundary)
    (k : ℕ) (hk : k < (commonKnots upper lower).card - 1)
    {q : unitInterval} (hq : q ∈ commonKnots upper lower)
    (hleft : commonPartitionGrid upper lower k < q) :
    commonPartitionGrid upper lower (k + 1) ≤ q := by
  let knots := commonKnots upper lower
  let e := knots.orderEmbOfFin rfl
  have hk : k < knots.card - 1 := by simpa [knots] using hk
  have hnonempty : knots.Nonempty := by
    simpa [knots] using commonKnots_nonempty upper lower
  have hcard : knots.card - 1 + 1 = knots.card :=
    Nat.sub_add_cancel (Finset.card_pos.mpr hnonempty)
  have hk' : k < knots.card - 1 := by simpa [knots] using hk
  let i : Fin knots.card := ⟨k, by omega⟩
  let j : Fin knots.card := (knots.orderIsoOfFin rfl).symm ⟨q, hq⟩
  have hi : commonPartitionGrid upper lower k = e i := by
    simpa [i, e, knots] using commonPartitionGrid_eq_orderEmb upper lower k hk
  have hj : e j = q := by
    simp [j, e, Finset.orderEmbOfFin]
  have hij : i < j := by
    apply e.strictMono.lt_iff_lt.mp
    calc
      e i = commonPartitionGrid upper lower k := hi.symm
      _ < q := hleft
      _ = e j := hj.symm
  let iNext : Fin knots.card := ⟨k + 1, by omega⟩
  have hiNext : commonPartitionGrid upper lower (k + 1) = e iNext := by
    simpa [iNext, e, knots] using
      commonPartitionGrid_succ_eq_orderEmb upper lower k hk
  have hij' : k < j.val := by
    have h := Fin.mk_lt_mk.mp hij
    change k < j.val at h
    exact h
  have hiNextLe : iNext ≤ j := by
    apply Fin.mk_le_mk.mpr
    change k + 1 ≤ j.val
    exact Nat.succ_le_of_lt hij'
  calc
    commonPartitionGrid upper lower (k + 1) = e iNext := hiNext
    _ ≤ e j := e.monotone hiNextLe
    _ = q := hj

/-- A step boundary is constant on each open cell of the common finite
partition. The right-continuous value at the left knot is the level used on
that cell. -/
theorem eval_eq_rightTrace_on_commonPartitionCell (b upper lower : StepBoundary)
    (hknots : ∀ q ∈ b.knots, q ∈ commonKnots upper lower)
    (k : ℕ) (hk : k < (commonKnots upper lower).card - 1)
    {q : unitInterval}
    (hleft : commonPartitionGrid upper lower k < q)
    (hright : q < commonPartitionGrid upper lower (k + 1)) :
    b.eval q = b.rightTrace (commonPartitionGrid upper lower k) := by
  rw [rightTrace_eq_eval]
  change b.levels (b.levelIndex q) =
    b.levels (b.levelIndex (commonPartitionGrid upper lower k))
  apply congrArg b.levels
  apply Fin.ext
  unfold levelIndex
  apply congrArg Finset.card
  ext r
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hr, hrq⟩
    by_cases hrl : r ≤ commonPartitionGrid upper lower k
    · exact ⟨hr, hrl⟩
    · have hkr : commonPartitionGrid upper lower k < r := lt_of_not_ge hrl
      have hnext := commonPartitionGrid_succ_le_of_mem upper lower k hk
        (hknots r hr) hkr
      exact False.elim <| (not_lt_of_ge (hnext.trans hrq)) hright
  · rintro ⟨hr, hrl⟩
    exact ⟨hr, hrl.trans (le_of_lt hleft)⟩

/-- The level immediately to the left of a cell's right knot is the level
used throughout the open cell. This identifies the incoming trace at a jump
with the preceding cell's constant boundary value. -/
theorem leftTrace_eq_rightTrace_on_precedingCommonCell
    (b upper lower : StepBoundary)
    (hknots : ∀ q ∈ b.knots, q ∈ commonKnots upper lower)
    (i : Fin ((commonKnots upper lower).card - 1)) :
    b.leftTrace (commonPartitionGrid upper lower (i.val + 1)) =
      b.rightTrace (commonPartitionGrid upper lower i.val) := by
  let left := commonPartitionGrid upper lower i.val
  let right := commonPartitionGrid upper lower (i.val + 1)
  have hlt : left < right := by
    exact commonPartitionGrid_strictSucc upper lower i.val i.isLt
  obtain ⟨s, hleft, hright⟩ := exists_between hlt
  have hgap : ∀ q ∈ b.knots, q < right → q ≤ left := by
    intro q hq hqr
    have hqCommon := hknots q hq
    by_contra hnot
    have hleftq : left < q := lt_of_not_ge hnot
    have hnextq := commonPartitionGrid_succ_le_of_mem
      upper lower i.val i.isLt hqCommon hleftq
    exact (not_lt_of_ge hnextq) hqr
  have hleftEval : b.eval s = b.leftTrace right :=
    b.eval_eq_leftTrace_of_between hleft hright hgap
  have hrightEval : b.eval s = b.rightTrace left :=
    b.eval_eq_rightTrace_on_commonPartitionCell upper lower hknots
      i.val i.isLt hleft hright
  exact hleftEval.symm.trans hrightEval

theorem mem_commonKnots_of_mem_upper (upper lower : StepBoundary)
    {t : unitInterval} (ht : t ∈ upper.knots) :
    t ∈ commonKnots upper lower := by
  simp [commonKnots, ht]

theorem mem_commonKnots_of_mem_lower (upper lower : StepBoundary)
    {t : unitInterval} (ht : t ∈ lower.knots) :
    t ∈ commonKnots upper lower := by
  simp [commonKnots, ht]

/-- The next common partition point after a nonterminal point. -/
noncomputable def nextCommonKnot (upper lower : StepBoundary)
    (t : unitInterval) (htop : t ≠ ⊤) : unitInterval :=
  (commonKnots upper lower |>.filter fun q => t < q).min'
    (by
      refine ⟨⊤, Finset.mem_filter.mpr ⟨top_mem_commonKnots upper lower,
        lt_top_iff_ne_top.mpr htop⟩⟩)

theorem nextCommonKnot_mem (upper lower : StepBoundary)
    (t : unitInterval) (htop : t ≠ ⊤) :
    nextCommonKnot upper lower t htop ∈ commonKnots upper lower := by
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).1

theorem lt_nextCommonKnot (upper lower : StepBoundary)
    (t : unitInterval) (htop : t ≠ ⊤) :
    t < nextCommonKnot upper lower t htop := by
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).2

/-- Every common partition point later than `t` lies at or after its
successor. -/
theorem nextCommonKnot_le_of_lt (upper lower : StepBoundary)
    (t q : unitInterval) (htop : t ≠ ⊤)
    (hq : q ∈ commonKnots upper lower) (htq : t < q) :
    nextCommonKnot upper lower t htop ≤ q := by
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hq, htq⟩)

/-- For a common-knot grid index, the least later common knot is exactly the
next grid value. -/
theorem nextCommonKnot_eq_commonPartitionGrid_succ
    (upper lower : StepBoundary)
    (i : Fin ((commonKnots upper lower).card - 1)) :
    nextCommonKnot upper lower (commonPartitionGrid upper lower i.val)
        (by
          intro htop
          have hstrict := commonPartitionGrid_strictSucc upper lower i.val i.isLt
          rw [htop] at hstrict
          exact (not_lt_of_ge le_top) hstrict) =
      commonPartitionGrid upper lower (i.val + 1) := by
  let left := commonPartitionGrid upper lower i.val
  let right := commonPartitionGrid upper lower (i.val + 1)
  have hleftRight : left < right := by
    exact commonPartitionGrid_strictSucc upper lower i.val i.isLt
  have hleftTop : left ≠ ⊤ := by
    intro htop
    simp [left, htop] at hleftRight
  have hrightMem : right ∈ commonKnots upper lower := by
    change commonPartitionGrid upper lower (i.val + 1) ∈ commonKnots upper lower
    rw [commonPartitionGrid_succ_eq_orderEmb upper lower i.val i.isLt]
    exact Finset.orderEmbOfFin_mem (commonKnots upper lower) rfl
      ⟨i.val + 1, by
        have hcard := Nat.sub_add_cancel
          (Finset.card_pos.mpr (commonKnots_nonempty upper lower))
        omega⟩
  have hnextLe : nextCommonKnot upper lower left hleftTop ≤ right :=
    nextCommonKnot_le_of_lt upper lower left right hleftTop hrightMem hleftRight
  have hrightLe : right ≤ nextCommonKnot upper lower left hleftTop := by
    obtain ⟨j, hj⟩ := exists_fin_commonPartitionGrid_eq upper lower
      (nextCommonKnot_mem upper lower left hleftTop)
    have hindex : i.val < j.val := by
      by_contra hnot
      have hji : j.val ≤ i.val := Nat.le_of_not_gt hnot
      have hgridLe := monotone_commonPartitionGrid upper lower hji
      rw [hj] at hgridLe
      exact (not_le_of_gt (lt_nextCommonKnot upper lower left hleftTop)) hgridLe
    have hsuccLe : i.val + 1 ≤ j.val := by omega
    calc
      right ≤ commonPartitionGrid upper lower j.val := by
        exact monotone_commonPartitionGrid upper lower hsuccLe
      _ = nextCommonKnot upper lower left hleftTop := hj
  exact le_antisymm hnextLe hrightLe

/-- A nonterminal time has a last common partition point strictly before it. -/
theorem exists_prev_commonKnot (upper lower : StepBoundary)
    {s : unitInterval} (hs : ⊥ < s) :
    ∃ p ∈ commonKnots upper lower, p < s ∧
      ∀ q ∈ commonKnots upper lower, q < s → q ≤ p := by
  classical
  let knots := commonKnots upper lower
  let prior := knots.filter fun q => q < s
  let candidates := insert (⊥ : unitInterval) prior
  have hne : candidates.Nonempty := ⟨⊥, Finset.mem_insert_self _ _⟩
  let p := candidates.max' hne
  have hpmem : p ∈ candidates := Finset.max'_mem _ _
  have hps : p < s := by
    rcases Finset.mem_insert.mp hpmem with hp | hp
    · simpa [hp] using hs
    · exact (Finset.mem_filter.mp hp).2
  have hpknots : p ∈ knots := by
    rcases Finset.mem_insert.mp hpmem with hp | hp
    · simp [hp, knots, bot_mem_commonKnots]
    · exact (Finset.mem_filter.mp hp).1
  refine ⟨p, hpknots, hps, ?_⟩
  intro q hq hqs
  have hqprior : q ∈ prior := Finset.mem_filter.mpr ⟨hq, hqs⟩
  exact Finset.le_max' _ _ (Finset.mem_insert_of_mem hqprior)

/-- A time interval belonging to one cell of the common partition. -/
noncomputable def commonCell (upper lower : StepBoundary) (t : unitInterval) :
    Set unitInterval :=
  if htop : t = ⊤ then ∅ else
    Set.Ioo t (nextCommonKnot upper lower t htop)

/-- The union of all cells indexed by nonterminal common partition points. -/
noncomputable def commonCellUnion (upper lower : StepBoundary) :
    Set unitInterval :=
  ⋃ (t : unitInterval)
      (_ : t ∈ ((commonKnots upper lower).erase ⊤ : Set unitInterval)),
    commonCell upper lower t

/-- The open cells are pairwise disjoint. -/
theorem pairwiseDisjoint_commonCells (upper lower : StepBoundary) :
  Set.PairwiseDisjoint (↑((commonKnots upper lower).erase ⊤))
      (commonCell upper lower) := by
  intro p hp q hq hpq
  change Disjoint (commonCell upper lower p) (commonCell upper lower q)
  rw [Set.disjoint_left]
  intro s hps hqs
  have ⟨hpTop, hpMem⟩ := Finset.mem_erase.mp hp
  have ⟨hqTop, hqMem⟩ := Finset.mem_erase.mp hq
  have hpCell : p < s ∧ s < nextCommonKnot upper lower p hpTop := by
    simpa [commonCell, hpTop] using hps
  have hqCell : q < s ∧ s < nextCommonKnot upper lower q hqTop := by
    simpa [commonCell, hqTop] using hqs
  rcases lt_or_gt_of_ne hpq with hpq' | hqp'
  · have hnext : nextCommonKnot upper lower p hpTop ≤ q :=
      nextCommonKnot_le_of_lt upper lower p q hpTop hqMem hpq'
    exact (not_lt_of_ge (le_of_lt (lt_of_lt_of_le hpCell.2 hnext))) hqCell.1
  · have hnext : nextCommonKnot upper lower q hqTop ≤ p :=
      nextCommonKnot_le_of_lt upper lower q p hqTop hpMem hqp'
    exact (not_lt_of_ge (le_of_lt (lt_of_lt_of_le hqCell.2 hnext))) hpCell.1

/-- The union of the common open cells is the interior of the time interval
with all common partition points removed. -/
theorem iUnion_commonCells_eq (upper lower : StepBoundary) :
    commonCellUnion upper lower =
      Set.Ioo ⊥ ⊤ \ (commonKnots upper lower : Set unitInterval) := by
  ext s
  constructor
  · rw [commonCellUnion, Set.mem_iUnion₂]
    rintro ⟨t, ht, hs⟩
    have ⟨htop, htmem⟩ := Finset.mem_erase.mp ht
    have hcell : t < s ∧ s < nextCommonKnot upper lower t htop := by
      simpa [commonCell, htop] using hs
    have hnextmem : nextCommonKnot upper lower t htop ∈
        commonKnots upper lower := nextCommonKnot_mem upper lower t htop
    refine ⟨⟨lt_of_le_of_lt bot_le hcell.1,
      lt_of_lt_of_le hcell.2 le_top⟩, ?_⟩
    intro hsMem
    have hnextle := nextCommonKnot_le_of_lt upper lower t s htop hsMem hcell.1
    exact (not_lt_of_ge hnextle) hcell.2
  · rintro ⟨⟨hsbot, hstop⟩, hsnot⟩
    obtain ⟨t, htmem, hts, htmax⟩ :=
      exists_prev_commonKnot upper lower hsbot
    have htop : t ≠ ⊤ := ne_of_lt (lt_trans hts hstop)
    have hnextgt : t < nextCommonKnot upper lower t htop :=
      lt_nextCommonKnot upper lower t htop
    have hnextmem : nextCommonKnot upper lower t htop ∈
        commonKnots upper lower := nextCommonKnot_mem upper lower t htop
    have hstnext : s < nextCommonKnot upper lower t htop := by
      by_contra hnot
      have hle : nextCommonKnot upper lower t htop ≤ s := le_of_not_gt hnot
      have hne : nextCommonKnot upper lower t htop ≠ s := by
        intro heq
        exact hsnot (heq ▸ hnextmem)
      have hlt : nextCommonKnot upper lower t htop < s := lt_of_le_of_ne hle hne
      exact (not_lt_of_ge (htmax _ hnextmem hlt)) hnextgt
    have htErase : t ∈ (commonKnots upper lower).erase ⊤ :=
      Finset.mem_erase.mpr ⟨htop, htmem⟩
    rw [commonCellUnion, Set.mem_iUnion₂]
    refine ⟨t, htErase, ?_⟩
    simpa [commonCell, htop] using (show s ∈ Set.Ioo t
      (nextCommonKnot upper lower t htop) from ⟨hts, hstnext⟩)

/-- There is no common partition point strictly between a partition point and
its successor. -/
theorem no_commonKnot_between_next (upper lower : StepBoundary)
    (t q : unitInterval) (htop : t ≠ ⊤)
    (hq : q ∈ commonKnots upper lower) (htq : t < q)
    (hqn : q < nextCommonKnot upper lower t htop) : False := by
  exact (not_lt_of_ge (nextCommonKnot_le_of_lt upper lower t q htop hq htq)) hqn

/-- A boundary whose knots lie in the common partition is constant on the
open cell from a partition point to its successor. The value at the left
endpoint is the right-continuous level, so jumps at that endpoint are
assigned to the cell on its right. -/
theorem eval_eq_rightTrace_on_nextCell (b upper lower : StepBoundary)
    (hknots : ∀ q ∈ b.knots, q ∈ commonKnots upper lower)
    (t s : unitInterval)
    (htop : t ≠ ⊤) (hts : t < s)
    (hs : s < nextCommonKnot upper lower t htop) :
    b.eval s = b.rightTrace t := by
  apply b.eval_eq_rightTrace_of_between hts hs
  intro q hq htq
  exact nextCommonKnot_le_of_lt upper lower t q htop
    (hknots q hq) htq

theorem upper_eval_eq_rightTrace_on_nextCell (upper lower : StepBoundary)
    (t s : unitInterval)
    (htop : t ≠ ⊤) (hts : t < s)
    (hs : s < nextCommonKnot upper lower t htop) :
    upper.eval s = upper.rightTrace t :=
  eval_eq_rightTrace_on_nextCell upper upper lower
    (fun _ hq => mem_commonKnots_of_mem_upper upper lower hq)
    t s htop hts hs

theorem lower_eval_eq_rightTrace_on_nextCell (upper lower : StepBoundary)
    (t s : unitInterval)
    (htop : t ≠ ⊤) (hts : t < s)
    (hs : s < nextCommonKnot upper lower t htop) :
    lower.eval s = lower.rightTrace t :=
  eval_eq_rightTrace_on_nextCell lower upper lower
    (fun _ hq => mem_commonKnots_of_mem_lower upper lower hq)
    t s htop hts hs

end StepBoundary

/-- The left endpoint index of a consecutive common-partition cell. -/
def commonPartitionCellLeftKnotIndex (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    Fin (StepBoundary.commonKnots upper lower).card :=
  ⟨i.val, by omega⟩

/-- The right endpoint index of a consecutive common-partition cell. -/
def commonPartitionCellRightKnotIndex (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    Fin (StepBoundary.commonKnots upper lower).card :=
  ⟨i.val + 1, by omega⟩

end Skorokhod.PathClass.StepCorridor

end

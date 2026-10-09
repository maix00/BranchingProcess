/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Partition.LowerCores
public import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Energy

/-!
# Finite inner corridors approximating step-boundary widths

This file supplies the geometric approximation needed after the finite-cell
lower-rate estimate. A real interval can be chosen inside an extended-real
interval, outside prescribed compact endpoint cores, and with width as close
to the full interval width as desired. Infinite boundary levels allow
arbitrarily large finite widths.
-/

open Filter MeasureTheory
open Skorokhod.PathClass.StepCorridor
open scoped NNReal Topology

@[expose] public section

namespace Skorokhod.PathClass.StepCorridor

/-- A finite open interval inside an extended-real interval can be chosen to
contain a prescribed compact subinterval and to have any width below the
available width. If either outer endpoint is infinite, every finite target
width is available. -/
theorem exists_innerRealInterval_with_width
    {L U : EReal} {a b target : ℝ}
    (hLa : L < (a : EReal)) (hab : a < b) (hbU : (b : EReal) < U)
    (htarget : 0 < target)
    (hwidth : L = ⊥ ∨ U = ⊤ ∨ target < U.toReal - L.toReal) :
    ∃ lo hi : ℝ,
      L < (lo : EReal) ∧ lo < a ∧ b < hi ∧ (hi : EReal) < U ∧
        target < hi - lo := by
  by_cases hLbot : L = ⊥
  · subst L
    by_cases hUtop : U = ⊤
    · subst U
      refine ⟨a - target - 1, b + target + 1, ?_, ?_, ?_, ?_, ?_⟩
      · exact EReal.bot_lt_coe _
      · linarith
      · linarith
      · exact EReal.coe_lt_top _
      · linarith
    · have hUbot : U ≠ ⊥ := by
        intro h
        subst U
        exact (lt_asymm (EReal.bot_lt_coe b) hbU).elim
      have hUeq : (U.toReal : EReal) = U := EReal.coe_toReal hUtop hUbot
      have hbReal : b < U.toReal := by
        apply EReal.coe_lt_coe_iff.mp
        simpa [hUeq] using hbU
      let hi := (b + U.toReal) / 2
      let lo := min (a - 1) (hi - target - 1)
      refine ⟨lo, hi, ?_, ?_, ?_, ?_, ?_⟩
      · exact EReal.bot_lt_coe _
      · change min (a - 1) (hi - target - 1) < a
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      · dsimp [hi]
        linarith
      · rw [← hUeq]
        exact EReal.coe_lt_coe_iff.mpr (by dsimp [hi]; linarith)
      · have hlo : lo ≤ hi - target - 1 := min_le_right _ _
        linarith
  · by_cases hUtop : U = ⊤
    · subst U
      have hLtop : L ≠ ⊤ := by
        intro h
        subst L
        exact (lt_asymm hLa (EReal.coe_lt_top a)).elim
      have hLeq : (L.toReal : EReal) = L :=
        EReal.coe_toReal hLtop hLbot
      have hLReal : L.toReal < a := by
        apply EReal.coe_lt_coe_iff.mp
        simpa [hLeq] using hLa
      let lo := (L.toReal + a) / 2
      let hi := b + target + 1
      refine ⟨lo, hi, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← hLeq]
        exact EReal.coe_lt_coe_iff.mpr (by dsimp [lo]; linarith)
      · dsimp [lo]
        linarith
      · dsimp [hi]
        linarith
      · exact EReal.coe_lt_top _
      · dsimp [lo, hi]
        linarith
    · have hfinite : target < U.toReal - L.toReal := by
        rcases hwidth with h | h | h
        · exact (hLbot h).elim
        · exact (hUtop h).elim
        · exact h
      have hLtop : L ≠ ⊤ := by
        intro h
        subst L
        exact (lt_asymm hLa (EReal.coe_lt_top a)).elim
      have hUbot : U ≠ ⊥ := by
        intro h
        subst U
        exact (lt_asymm (EReal.bot_lt_coe b) hbU).elim
      have hLeq : (L.toReal : EReal) = L :=
        EReal.coe_toReal hLtop hLbot
      have hUeq : (U.toReal : EReal) = U :=
        EReal.coe_toReal hUtop hUbot
      have hLReal : L.toReal < a := by
        apply EReal.coe_lt_coe_iff.mp
        simpa [hLeq] using hLa
      have hUReal : b < U.toReal := by
        apply EReal.coe_lt_coe_iff.mp
        simpa [hUeq] using hbU
      let gap := U.toReal - L.toReal - target
      let δ := min (min ((a - L.toReal) / 2) ((U.toReal - b) / 2)) (gap / 4)
      have hgap : 0 < gap := by dsimp [gap]; linarith [hfinite]
      have hδ : 0 < δ := by
        apply lt_min
        · exact lt_min (by linarith [hLReal]) (by linarith [hUReal])
        · exact by linarith [hgap]
      let lo := L.toReal + δ
      let hi := U.toReal - δ
      refine ⟨lo, hi, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← hLeq]
        exact EReal.coe_lt_coe_iff.mpr (by dsimp [lo]; linarith)
      · dsimp [lo]
        have hδleft : δ ≤ (a - L.toReal) / 2 :=
          (min_le_left _ _).trans (min_le_left _ _)
        linarith
      · dsimp [hi]
        have hδright : δ ≤ (U.toReal - b) / 2 :=
          (min_le_left _ _).trans (min_le_right _ _)
        linarith
      · rw [← hUeq]
        exact EReal.coe_lt_coe_iff.mpr (by dsimp [hi]; linarith)
      · have hδgap : δ ≤ gap / 4 := min_le_right _ _
        dsimp [lo, hi, gap]
        linarith

/-- On a common partition cell, finite inner boundary levels can be chosen
to contain both endpoint cores and to have any prescribed width below the
cell's full corridor width. Infinite outer traces allow any finite target
width. -/
theorem exists_commonPartitionCellInnerBounds_withWidth
    (upper lower : StepBoundary)
    (center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ)
    (hcores : ∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      center j - radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val) ∧
      center j + radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val))
    (hradiusNonneg : ∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      0 ≤ radius j)
    (hradiusStep : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      radius (commonPartitionCellLeftKnotIndex upper lower i) <
        radius (commonPartitionCellRightKnotIndex upper lower i))
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    {target : ℝ} (htarget : 0 < target)
    (hwidth :
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊥ ∨
      upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊤ ∨
      target <
        (upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
          (lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal) :
    ∃ lo hi : ℝ,
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) < lo ∧
      lo < center (commonPartitionCellLeftKnotIndex upper lower i) -
        radius (commonPartitionCellLeftKnotIndex upper lower i) ∧
      lo < center (commonPartitionCellRightKnotIndex upper lower i) -
        radius (commonPartitionCellRightKnotIndex upper lower i) ∧
      center (commonPartitionCellLeftKnotIndex upper lower i) +
        radius (commonPartitionCellLeftKnotIndex upper lower i) < hi ∧
      center (commonPartitionCellRightKnotIndex upper lower i) +
        radius (commonPartitionCellRightKnotIndex upper lower i) < hi ∧
      hi < upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) ∧
      target < hi - lo := by
  let i₀ := commonPartitionCellLeftKnotIndex upper lower i
  let i₁ := commonPartitionCellRightKnotIndex upper lower i
  let left := StepBoundary.commonPartitionGrid upper lower i.val
  let right := StepBoundary.commonPartitionGrid upper lower (i.val + 1)
  let lowerTrace := lower.rightTrace left
  let upperTrace := upper.rightTrace left
  let lower₀ := center i₀ - radius i₀
  let lower₁ := center i₁ - radius i₁
  let upper₀ := center i₀ + radius i₀
  let upper₁ := center i₁ + radius i₁
  have htraceLower : lower.leftTrace right = lowerTrace :=
    StepBoundary.leftTrace_eq_rightTrace_on_precedingCommonCell lower upper lower
      (fun q hq => StepBoundary.mem_commonKnots_of_mem_lower upper lower hq) i
  have htraceUpper : upper.leftTrace right = upperTrace :=
    StepBoundary.leftTrace_eq_rightTrace_on_precedingCommonCell upper upper lower
      (fun q hq => StepBoundary.mem_commonKnots_of_mem_upper upper lower hq) i
  have hlower₀' : max (lower.leftTrace left) (lower.rightTrace left) <
      (lower₀ : EReal) := by
    have h := (hcores i₀).1.1
    change max (lower.leftTrace left) (lower.rightTrace left) <
      (lower₀ : EReal) at h
    exact h
  have hlower₀ : lowerTrace < (lower₀ : EReal) := by
    change lower.rightTrace left < (lower₀ : EReal)
    exact (le_max_right _ _).trans_lt hlower₀'
  have hlower₁' : max (lower.leftTrace right) (lower.rightTrace right) <
      (lower₁ : EReal) := by
    have h := (hcores i₁).1.1
    change max (lower.leftTrace right) (lower.rightTrace right) <
      (lower₁ : EReal) at h
    exact h
  have hlower₁ : lowerTrace < (lower₁ : EReal) := by
    have h := (le_max_left _ _).trans_lt hlower₁'
    rw [htraceLower] at h
    exact h
  have hupper₀' : (upper₀ : EReal) <
      min (upper.leftTrace left) (upper.rightTrace left) := by
    have h := (hcores i₀).2.2
    change (upper₀ : EReal) <
      min (upper.leftTrace left) (upper.rightTrace left) at h
    exact h
  have hupper₀ : (upper₀ : EReal) < upperTrace := by
    change (upper₀ : EReal) < upper.rightTrace left
    exact (lt_of_lt_of_le hupper₀' (min_le_right _ _))
  have hupper₁' : (upper₁ : EReal) <
      min (upper.leftTrace right) (upper.rightTrace right) := by
    have h := (hcores i₁).2.2
    change (upper₁ : EReal) <
      min (upper.leftTrace right) (upper.rightTrace right) at h
    exact h
  have hupper₁ : (upper₁ : EReal) < upperTrace := by
    have h := lt_of_lt_of_le hupper₁' (min_le_left _ _)
    rw [htraceUpper] at h
    exact h
  let a := min lower₀ lower₁
  let b := max upper₀ upper₁
  have hla : lowerTrace < (a : EReal) := by
    dsimp [a]
    by_cases h : lower₀ ≤ lower₁
    · rw [min_eq_left h]
      exact hlower₀
    · rw [min_eq_right (le_of_not_ge h)]
      exact hlower₁
  have hub : (b : EReal) < upperTrace := by
    dsimp [b]
    by_cases h : upper₀ ≤ upper₁
    · rw [max_eq_right h]
      exact hupper₁
    · rw [max_eq_left (le_of_not_ge h)]
      exact hupper₀
  have hradRightPos : 0 < radius i₁ :=
    lt_of_le_of_lt (hradiusNonneg i₀) (hradiusStep i)
  have hab : a < b := by
    calc
      a ≤ lower₁ := by dsimp [a]; exact min_le_right _ _
      _ < upper₁ := by dsimp [lower₁, upper₁]; linarith
      _ ≤ b := by dsimp [b]; exact le_max_right _ _
  obtain ⟨lo, hi, hLlo, hloA, hBhi, hhiU, htargetWidth⟩ :=
    exists_innerRealInterval_with_width hla hab hub htarget hwidth
  refine ⟨lo, hi, ?_, ?_, ?_, ?_, ?_, ?_, htargetWidth⟩
  · exact hLlo
  · exact (lt_of_lt_of_le hloA (min_le_left _ _))
  · exact (lt_of_lt_of_le hloA (min_le_right _ _))
  · exact (lt_of_le_of_lt (le_max_left _ _) hBhi)
  · exact (lt_of_le_of_lt (le_max_right _ _) hBhi)
  · exact hhiU

/-- Endpoint cores and finite inner bounds can be chosen simultaneously on
the entire common partition, with a separately prescribed lower bound on
each cell width. The targets may be arbitrarily large on cells with an
infinite boundary trace. -/
theorem exists_commonPartitionInnerGeometry_withWidth
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower)
    (target : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (htarget : ∀ i, 0 < target i)
    (hwidth : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊥ ∨
      upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊤ ∨
      target i <
        (upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
          (lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal) :
    ∃ center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ,
      ∃ innerLower innerUpper :
        Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ,
      center ⟨0, by
        have hcard := Finset.card_pos.mpr
          (StepBoundary.commonKnots_nonempty upper lower)
        omega⟩ = 0 ∧
      radius ⟨0, by
        have hcard := Finset.card_pos.mpr
          (StepBoundary.commonKnots_nonempty upper lower)
        omega⟩ = 0 ∧
      (∀ j, 0 ≤ radius j) ∧
      (∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        radius (commonPartitionCellLeftKnotIndex upper lower i) <
          radius (commonPartitionCellRightKnotIndex upper lower i)) ∧
      (∀ j : Fin (StepBoundary.commonKnots upper lower).card,
        center j - radius j ∈ selValues upper lower
          (StepBoundary.commonPartitionGrid upper lower j.val) ∧
        center j + radius j ∈ selValues upper lower
          (StepBoundary.commonPartitionGrid upper lower j.val)) ∧
      (∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) <
            innerLower i ∧
          innerLower i <
            center (commonPartitionCellLeftKnotIndex upper lower i) -
              radius (commonPartitionCellLeftKnotIndex upper lower i) ∧
          innerLower i <
            center (commonPartitionCellRightKnotIndex upper lower i) -
              radius (commonPartitionCellRightKnotIndex upper lower i) ∧
          center (commonPartitionCellLeftKnotIndex upper lower i) +
              radius (commonPartitionCellLeftKnotIndex upper lower i) <
            innerUpper i ∧
          center (commonPartitionCellRightKnotIndex upper lower i) +
              radius (commonPartitionCellRightKnotIndex upper lower i) <
            innerUpper i ∧
          innerUpper i <
            upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)) ∧
      (∀ i, target i < innerUpper i - innerLower i) := by
  let center : Fin (StepBoundary.commonKnots upper lower).card → ℝ :=
    commonPartitionCoreCenter upper lower hsep
  let radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ :=
    commonPartitionCoreRadius upper lower hstart hsep
  have hcenter0 : center ⟨0, by
      have hcard := Finset.card_pos.mpr
        (StepBoundary.commonKnots_nonempty upper lower)
      omega⟩ = 0 := by
    simp [center, commonPartitionCoreCenter]
  have hradius0 : radius ⟨0, by
      have hcard := Finset.card_pos.mpr
        (StepBoundary.commonKnots_nonempty upper lower)
      omega⟩ = 0 := by
    exact commonPartitionCoreRadius_zero upper lower hstart hsep
  have hradiusNonneg : ∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      0 ≤ radius j := by
    intro j
    exact commonPartitionCoreRadius_nonneg upper lower hstart hsep j
  have hstep : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      radius (commonPartitionCellLeftKnotIndex upper lower i) <
        radius (commonPartitionCellRightKnotIndex upper lower i) := by
    intro i
    let i₀ := commonPartitionCellLeftKnotIndex upper lower i
    let i₁ := commonPartitionCellRightKnotIndex upper lower i
    change (i.val : ℝ) * commonPartitionCoreRadiusStep upper lower hstart hsep <
      ((i.val + 1 : ℕ) : ℝ) * commonPartitionCoreRadiusStep upper lower hstart hsep
    exact mul_lt_mul_of_pos_right (by exact_mod_cast Nat.lt_succ_self i.val)
      (commonPartitionCoreRadiusStep_pos upper lower hstart hsep)
  have hcores : ∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      center j - radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val) ∧
      center j + radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val) := by
    intro j
    exact commonPartitionCoreRadius_mem upper lower hstart hsep j
  have hcell : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      ∃ lo hi : ℝ,
        lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) < lo ∧
        lo < center (commonPartitionCellLeftKnotIndex upper lower i) -
          radius (commonPartitionCellLeftKnotIndex upper lower i) ∧
        lo < center (commonPartitionCellRightKnotIndex upper lower i) -
          radius (commonPartitionCellRightKnotIndex upper lower i) ∧
        center (commonPartitionCellLeftKnotIndex upper lower i) +
          radius (commonPartitionCellLeftKnotIndex upper lower i) < hi ∧
        center (commonPartitionCellRightKnotIndex upper lower i) +
          radius (commonPartitionCellRightKnotIndex upper lower i) < hi ∧
        hi < upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) ∧
        target i < hi - lo := by
    intro i
    exact exists_commonPartitionCellInnerBounds_withWidth upper lower center radius
      hcores hradiusNonneg hstep i (htarget i) (hwidth i)
  choose innerLower innerUpper hcell using hcell
  have hgeometry : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) <
          innerLower i ∧
        innerLower i <
          center (commonPartitionCellLeftKnotIndex upper lower i) -
            radius (commonPartitionCellLeftKnotIndex upper lower i) ∧
        innerLower i <
          center (commonPartitionCellRightKnotIndex upper lower i) -
            radius (commonPartitionCellRightKnotIndex upper lower i) ∧
        center (commonPartitionCellLeftKnotIndex upper lower i) +
            radius (commonPartitionCellLeftKnotIndex upper lower i) <
          innerUpper i ∧
        center (commonPartitionCellRightKnotIndex upper lower i) +
            radius (commonPartitionCellRightKnotIndex upper lower i) <
          innerUpper i ∧
        innerUpper i <
          upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) := by
    intro i
    rcases hcell i with ⟨h₁, h₂, h₃, h₄, h₅, h₆, _⟩
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
  refine ⟨center, radius, innerLower, innerUpper, hcenter0, hradius0,
    hradiusNonneg, hstep, hcores, hgeometry, ?_⟩
  intro i
  exact (hcell i).2.2.2.2.2.2

end Skorokhod.PathClass.StepCorridor

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.PartitionEndpoint

/-!
# Deterministic lower gluing for a floor-partitioned random walk

This module shows that local contracted-corridor and endpoint-core events on
the floor-rounded cells imply the global strict step-corridor event.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

open ProbabilityTheory.RandomWalk
open Skorokhod.PathClass.StepCorridor
open Skorokhod.PathClass.StepCorridor

private theorem stepBoundary_eval_eq_rightTrace_of_mem_commonPartitionCell
    (b upper lower : StepBoundary)
    (hknots : ∀ q ∈ b.knots, q ∈ StepBoundary.commonKnots upper lower)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    {t : unitInterval}
    (hleft : StepBoundary.commonPartitionGrid upper lower i.val ≤ t)
    (hright : t < StepBoundary.commonPartitionGrid upper lower (i.val + 1)) :
    b.eval t = b.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) := by
  by_cases hteq : t = StepBoundary.commonPartitionGrid upper lower i.val
  · subst t
    exact (StepBoundary.rightTrace_eq_eval b _).symm
  · exact StepBoundary.eval_eq_rightTrace_on_commonPartitionCell
      b upper lower hknots i.val i.isLt
      (lt_of_le_of_ne hleft (Ne.symm hteq)) hright

/-- If the initial condition, knot cores, and all local floor-cell
core-return events hold, then the normalized step path lies in the strict
global corridor. The half-open cells use the right trace at their left knot;
the endpoint-core induction handles the finitely many knot values. -/
theorem normalizedStepCadlagPathIcc_mem_corridorSet_of_partitionCellCoreReturnBlockEvents
    {n : ℕ} {scale : ℕ → ℝ} (hscale : 0 < scale n)
    (upper lower : StepBoundary)
    (center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ)
    (innerLower innerUpper :
      Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hcenter0 : ∀ j, j.val = 0 → center j = 0)
    (hradius0 : ∀ j, j.val = 0 → radius j = 0)
    (hradiusStep : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      radius (commonPartitionCellLeftKnotIndex upper lower i) <
        radius (commonPartitionCellRightKnotIndex upper lower i))
    (hcores : ∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      center j - radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val) ∧
      center j + radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val))
    (hgeometry : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) <
          (innerLower i : EReal) ∧
        (innerUpper i : EReal) <
          upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val))
    (hblocks : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      Combinatorics.Sequence.blockCoordinates
          (AdditivePath.blockStart (commonPartitionCellStepLengths n upper lower) i.val)
          (commonPartitionCellStepLengths n upper lower i.val) increment ∈
        {block | partitionCellCoreReturnBlockEvent
          (scale n * innerLower i) (scale n * innerUpper i)
          (scale n * center (commonPartitionCellLeftKnotIndex upper lower i))
          (scale n * radius (commonPartitionCellLeftKnotIndex upper lower i))
          (scale n * center (commonPartitionCellRightKnotIndex upper lower i))
          (scale n * radius (commonPartitionCellRightKnotIndex upper lower i)) block}) :
    RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
      Skorokhod.PathClass.StepCorridor.corridorSet upper lower := by
  let knotCount := (StepBoundary.commonKnots upper lower).card
  let lengths := commonPartitionCellStepLengths n upper lower
  have hcore := normalizedStepCadlagPathIcc_commonPartitionGrid_mem_core_of_blockEvents
    hscale upper lower center radius innerLower innerUpper hcenter0 hradius0
    (by simpa [commonPartitionCellLeftKnotIndex, commonPartitionCellRightKnotIndex]
      using hradiusStep) (by
        intro i
        simpa [commonPartitionCellLeftKnotIndex, commonPartitionCellRightKnotIndex]
          using hblocks i)
  have hpathValue (t : unitInterval) :
      RandomWalk.normalizedStepCadlagPathIcc scale n increment t =
        (scale n)⁻¹ * AdditivePath.displacement
          (commonPartitionFloorTimeIndex n t) increment := by
    change RandomWalk.normalizedStepPath scale n increment (t : ℝ) = _
    rfl
  have hcoreRaw (j : Fin knotCount) :
      AdditivePath.displacement
          (commonPartitionFloorTimeIndex n
            (StepBoundary.commonPartitionGrid upper lower j.val)) increment ∈
        Set.Icc (scale n * center j - scale n * radius j)
          (scale n * center j + scale n * radius j) := by
    have hnormalized := hcore j
    rw [normalizedStepCadlagPathIcc_commonPartitionGrid_apply] at hnormalized
    rcases hnormalized with ⟨hlo, hhi⟩
    constructor
    · calc
        scale n * center j - scale n * radius j =
            scale n * (center j - radius j) := by ring
        _ ≤ scale n * ((scale n)⁻¹ * AdditivePath.displacement
            (commonPartitionFloorTimeIndex n
              (StepBoundary.commonPartitionGrid upper lower j.val)) increment) :=
          mul_le_mul_of_nonneg_left hlo hscale.le
        _ = _ := by
          rw [← mul_assoc, mul_inv_cancel₀ hscale.ne', one_mul]
    · calc
        AdditivePath.displacement
            (commonPartitionFloorTimeIndex n
              (StepBoundary.commonPartitionGrid upper lower j.val)) increment =
            scale n * ((scale n)⁻¹ * AdditivePath.displacement
              (commonPartitionFloorTimeIndex n
                (StepBoundary.commonPartitionGrid upper lower j.val)) increment) := by
                rw [← mul_assoc, mul_inv_cancel₀ hscale.ne', one_mul]
        _ ≤ scale n * (center j + radius j) := mul_le_mul_of_nonneg_left hhi hscale.le
        _ = scale n * center j + scale n * radius j := by ring
  have knotCorridor (t : unitInterval) (ht : t ∈ StepBoundary.commonKnots upper lower) :
      lower.eval t <
          (RandomWalk.normalizedStepCadlagPathIcc scale n increment t : EReal) ∧
        (RandomWalk.normalizedStepCadlagPathIcc scale n increment t : EReal) <
          upper.eval t := by
    obtain ⟨j, hj⟩ := StepBoundary.exists_fin_commonPartitionGrid_eq upper lower ht
    have hcore' := hcore j
    have hlowCore : lower.rightTrace
        (StepBoundary.commonPartitionGrid upper lower j.val) <
          (center j - radius j : EReal) := by
      exact (le_max_right _ _).trans_lt (hcores j).1.1
    have hupperCore : (center j + radius j : EReal) <
        upper.rightTrace (StepBoundary.commonPartitionGrid upper lower j.val) := by
      exact (lt_of_lt_of_le (hcores j).2.2 (min_le_right _ _))
    have hpathCoreLower : (center j - radius j : EReal) ≤
        (RandomWalk.normalizedStepCadlagPathIcc scale n increment
          (StepBoundary.commonPartitionGrid upper lower j.val) : EReal) :=
      EReal.coe_le_coe_iff.mpr hcore'.1
    have hpathCoreUpper :
        (RandomWalk.normalizedStepCadlagPathIcc scale n increment
          (StepBoundary.commonPartitionGrid upper lower j.val) : EReal) ≤
          (center j + radius j : EReal) := EReal.coe_le_coe_iff.mpr hcore'.2
    constructor
    · calc
        lower.eval t = lower.rightTrace
            (StepBoundary.commonPartitionGrid upper lower j.val) := by
              rw [← hj, StepBoundary.rightTrace_eq_eval]
        _ < (center j - radius j : EReal) := hlowCore
        _ ≤ (RandomWalk.normalizedStepCadlagPathIcc scale n increment
            (StepBoundary.commonPartitionGrid upper lower j.val) : EReal) := hpathCoreLower
        _ = _ := by rw [hj]
    · calc
        (RandomWalk.normalizedStepCadlagPathIcc scale n increment t : EReal) =
            (RandomWalk.normalizedStepCadlagPathIcc scale n increment
              (StepBoundary.commonPartitionGrid upper lower j.val) : EReal) := by rw [hj]
        _ ≤ (center j + radius j : EReal) := hpathCoreUpper
        _ < upper.rightTrace (StepBoundary.commonPartitionGrid upper lower j.val) := hupperCore
        _ = upper.eval t := by rw [← hj, StepBoundary.rightTrace_eq_eval]
  have hcorridor (t : unitInterval) :
      lower.eval t <
          (RandomWalk.normalizedStepCadlagPathIcc scale n increment t : EReal) ∧
        (RandomWalk.normalizedStepCadlagPathIcc scale n increment t : EReal) <
          upper.eval t := by
    by_cases ht : t ∈ StepBoundary.commonKnots upper lower
    · exact knotCorridor t ht
    · have htbot : t ≠ ⊥ := by
        intro h
        apply ht
        simp [h]
      have httop : t ≠ ⊤ := by
        intro h
        apply ht
        simp [h]
      have hinterior : t ∈ Set.Ioo (⊥ : unitInterval) ⊤ :=
        ⟨bot_lt_iff_ne_bot.mpr htbot, lt_top_iff_ne_top.mpr httop⟩
      have hnotSet : t ∉ (StepBoundary.commonKnots upper lower : Set unitInterval) := by
        simpa using ht
      have hcellUnion : t ∈ StepBoundary.commonCellUnion upper lower :=
        (StepBoundary.iUnion_commonCells_eq upper lower).symm ▸
          ⟨hinterior, hnotSet⟩
      change t ∈ ⋃ (p : unitInterval)
        (_ : p ∈ ((StepBoundary.commonKnots upper lower).erase ⊤ : Set unitInterval)),
          StepBoundary.commonCell upper lower p at hcellUnion
      obtain ⟨p, hp, hpt⟩ := Set.mem_iUnion₂.mp hcellUnion
      rcases Finset.mem_erase.mp hp with ⟨hpTop, hpMem⟩
      have hcell : p < t ∧ t < StepBoundary.nextCommonKnot upper lower p hpTop := by
        simpa [StepBoundary.commonCell, hpTop] using hpt
      obtain ⟨j, hj⟩ := StepBoundary.exists_fin_commonPartitionGrid_eq
        upper lower hpMem
      have hjlt : j.val < knotCount - 1 := by
        by_contra hnotlt
        have hjlast : j.val = knotCount - 1 := by omega
        have hgridTop : StepBoundary.commonPartitionGrid upper lower j.val = ⊤ := by
          calc
            _ = StepBoundary.commonPartitionGrid upper lower (knotCount - 1) := by rw [hjlast]
            _ = ⊤ := StepBoundary.commonPartitionGrid_last upper lower
        exact hpTop (hj.symm.trans hgridTop)
      let i : Fin (knotCount - 1) := ⟨j.val, hjlt⟩
      have hleftStrict : StepBoundary.commonPartitionGrid upper lower i.val < t := by
        simpa [i, hj] using hcell.1
      have hnotTop : StepBoundary.commonPartitionGrid upper lower i.val ≠ ⊤ :=
        ne_of_lt (lt_of_lt_of_le
          (StepBoundary.commonPartitionGrid_strictSucc upper lower i.val i.isLt) le_top)
      have hcellNext : t < StepBoundary.nextCommonKnot upper lower
          (StepBoundary.commonPartitionGrid upper lower i.val) hnotTop := by
        subst p
        simpa [i] using hcell.2
      have hnextEq := StepBoundary.nextCommonKnot_eq_commonPartitionGrid_succ
        upper lower i
      have hrightStrict : t <
          StepBoundary.commonPartitionGrid upper lower (i.val + 1) := by
        simpa [hnextEq] using hcellNext
      let left := StepBoundary.commonPartitionGrid upper lower i.val
      let right := StepBoundary.commonPartitionGrid upper lower (i.val + 1)
      let start := commonPartitionFloorTimeIndex n left
      let stop := commonPartitionFloorTimeIndex n right
      let position := commonPartitionFloorTimeIndex n t
      have hleftTime : left ≤ t := hleftStrict.le
      have hrightTime : t ≤ right := hrightStrict.le
      have hstartPosition : start ≤ position := by
        exact commonPartitionFloorTimeIndex_mono n hleftTime
      have hpositionStop : position ≤ stop :=
        commonPartitionFloorTimeIndex_mono n hrightTime
      have hstart_eq : AdditivePath.blockStart lengths i.val = start := by
        simpa [start, left, lengths] using
          blockStart_commonPartitionCellStepLengths n upper lower i
      have hlength : lengths i.val = stop - start := by
        change (if h : i.val < (StepBoundary.commonKnots upper lower).card - 1 then
          commonPartitionFloorTimeIndex n
              (StepBoundary.commonPartitionGrid upper lower (i.val + 1)) -
            commonPartitionFloorTimeIndex n
              (StepBoundary.commonPartitionGrid upper lower i.val)
          else 0) = stop - start
        rw [dite_eq_left i.isLt]
      have hpositionEq : start + (position - start) = position :=
        Nat.add_sub_of_le hstartPosition
      have hoffset : position - start ≤ lengths i.val := by
        rw [hlength]
        omega
      let offset : Fin (lengths i.val + 1) :=
        ⟨position - start, Nat.lt_succ_of_le hoffset⟩
      have hstartCore := hcoreRaw (commonPartitionCellLeftKnotIndex upper lower i)
      have hblock := hblocks i
      change partitionCellCoreReturnBlockEvent
          (scale n * innerLower i) (scale n * innerUpper i)
          (scale n * center (commonPartitionCellLeftKnotIndex upper lower i))
          (scale n * radius (commonPartitionCellLeftKnotIndex upper lower i))
          (scale n * center (commonPartitionCellRightKnotIndex upper lower i))
          (scale n * radius (commonPartitionCellRightKnotIndex upper lower i))
          (Combinatorics.Sequence.blockCoordinates
            (AdditivePath.blockStart lengths i.val) (lengths i.val) increment) at hblock
      have hlocal := partitionCellCoreReturnBlockEvent_positions_mem
        (x := AdditivePath.displacement start increment)
        (by simpa [hstart_eq, left, commonPartitionCellLeftKnotIndex] using hstartCore)
        hblock offset
      have hpartial :
          Fin.partialSum
              (Combinatorics.Sequence.blockCoordinates
                (AdditivePath.blockStart lengths i.val) (lengths i.val) increment) offset =
            AdditivePath.blockSum start (position - start) increment := by
        rw [partialSum_blockCoordinates]
        simp [offset, hstart_eq]
      have hpositionDisplacement :
          AdditivePath.displacement position increment =
            AdditivePath.displacement start increment +
              Fin.partialSum
                (Combinatorics.Sequence.blockCoordinates
                  (AdditivePath.blockStart lengths i.val) (lengths i.val) increment) offset := by
        calc
          AdditivePath.displacement position increment =
              AdditivePath.displacement (start + (position - start)) increment := by
                rw [hpositionEq]
          _ = AdditivePath.displacement start increment +
                AdditivePath.blockSum start (position - start) increment :=
              AdditivePath.displacement_add_eq_add_blockSum start (position - start) increment
          _ = _ := by rw [← hpartial]
      have hrawLower : scale n * innerLower i <
          AdditivePath.displacement position increment := by
        simpa [hpositionDisplacement] using hlocal.1
      have hrawUpper : AdditivePath.displacement position increment <
          scale n * innerUpper i := by
        simpa [hpositionDisplacement] using hlocal.2
      have hrealLower : innerLower i <
          (scale n)⁻¹ * AdditivePath.displacement position increment := by
        have hraw : innerLower i * scale n < AdditivePath.displacement position increment :=
          by simpa [mul_comm] using hrawLower
        have h := (lt_div_iff₀ hscale).2 hraw
        simpa [div_eq_mul_inv, mul_comm] using h
      have hrealUpper : (scale n)⁻¹ * AdditivePath.displacement position increment <
          innerUpper i := by
        have hraw : AdditivePath.displacement position increment < innerUpper i * scale n :=
          by simpa [mul_comm] using hrawUpper
        have h := (div_lt_iff₀ hscale).2 hraw
        simpa [div_eq_mul_inv, mul_comm] using h
      have hpathLower : (innerLower i : EReal) <
          (RandomWalk.normalizedStepCadlagPathIcc scale n increment t : EReal) := by
        rw [hpathValue]
        exact EReal.coe_lt_coe_iff.mpr hrealLower
      have hpathUpper :
          (RandomWalk.normalizedStepCadlagPathIcc scale n increment t : EReal) <
            (innerUpper i : EReal) := by
        rw [hpathValue]
        exact EReal.coe_lt_coe_iff.mpr hrealUpper
      have hlowerEval := stepBoundary_eval_eq_rightTrace_of_mem_commonPartitionCell
        lower upper lower
        (fun q hq => StepBoundary.mem_commonKnots_of_mem_lower upper lower hq)
        i (by simpa [left] using hleftTime) (by simpa [right] using hrightStrict)
      have hupperEval := stepBoundary_eval_eq_rightTrace_of_mem_commonPartitionCell
        upper upper lower
        (fun q hq => StepBoundary.mem_commonKnots_of_mem_upper upper lower hq)
        i (by simpa [left] using hleftTime) (by simpa [right] using hrightStrict)
      constructor
      · rw [hlowerEval]
        exact (hgeometry i).1.trans hpathLower
      · rw [hupperEval]
        exact hpathUpper.trans (hgeometry i).2
  change RandomWalk.normalizedStepCadlagPathIcc scale n increment ⊥ = 0 ∧
    ∀ t, lower.eval t <
      (RandomWalk.normalizedStepCadlagPathIcc scale n increment t : EReal) ∧
      (RandomWalk.normalizedStepCadlagPathIcc scale n increment t : EReal) < upper.eval t
  exact ⟨by
    change RandomWalk.normalizedStepPath scale n increment (⊥ : unitInterval) = 0
    simp [RandomWalk.normalizedStepPath], hcorridor⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

end

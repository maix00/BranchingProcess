/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.SourcePartitionEvents
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.PartitionEndpoint

/-! # Endpoint-core gluing for the source terminal-left path -/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

open ProbabilityTheory.RandomWalk
open Skorokhod.PathClass.StepCorridor
open Skorokhod.PathClass.StepCorridor

/-- Endpoint-core events on source-length cells propagate the path into all
partition-knot cores. The final cell ends at `S_(n-1)`. -/
theorem sourceNormalizedStepCadlagPathIcc_commonPartitionGrid_mem_core_of_blockEvents
    {n : ℕ} {scale : ℕ → ℝ} (hn : 0 < n) (hscale : 0 < scale n)
    (upper lower : StepBoundary)
    (center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ)
    (innerLower innerUpper :
      Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (increment : ℕ → ℝ)
    (hcenter0 : ∀ j, j.val = 0 → center j = 0)
    (hradius0 : ∀ j, j.val = 0 → radius j = 0)
    (hradiusStep : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      radius ⟨i.val, by omega⟩ < radius ⟨i.val + 1, by omega⟩)
    (hblocks : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      Combinatorics.Sequence.blockCoordinates
          (AdditivePath.blockStart (sourcePartitionCellStepLengths n upper lower) i.val)
          (sourcePartitionCellStepLengths n upper lower i.val) increment ∈
        {block | partitionCellCoreReturnBlockEvent
          (scale n * innerLower i) (scale n * innerUpper i)
          (scale n * center ⟨i.val, by omega⟩)
          (scale n * radius ⟨i.val, by omega⟩)
          (scale n * center ⟨i.val + 1, by omega⟩)
          (scale n * radius ⟨i.val + 1, by omega⟩) block}) :
    ∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      sourceNormalizedStepCadlagPathIcc scale n increment
          (StepBoundary.commonPartitionGrid upper lower j.val) ∈
        Set.Icc (center j - radius j) (center j + radius j) := by
  let knotCount := (StepBoundary.commonKnots upper lower).card
  let cellCount := knotCount - 1
  let lengths := sourcePartitionCellStepLengths n upper lower
  have hcore : ∀ k : ℕ, (hk : k < knotCount) →
      sourceNormalizedStepCadlagPathIcc scale n increment
          (StepBoundary.commonPartitionGrid upper lower k) ∈
        Set.Icc (center ⟨k, hk⟩ - radius ⟨k, hk⟩)
          (center ⟨k, hk⟩ + radius ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero =>
        intro hk
        let j : Fin knotCount := ⟨0, hk⟩
        have hjcenter : center j = 0 := hcenter0 j rfl
        have hjradius : radius j = 0 := hradius0 j rfl
        have hgrid := StepBoundary.commonPartitionGrid_zero upper lower
        rw [hgrid]
        have hbotne : (⊥ : unitInterval) ≠ ⊤ := by norm_num [unitInterval]
        rw [sourceNormalizedStepCadlagPathIcc_apply_of_ne_top scale n increment hbotne]
        change RandomWalk.normalizedStepPath scale n increment 0 ∈
          Set.Icc (center j - radius j) (center j + radius j)
        rw [RandomWalk.normalizedStepPath_zero, hjcenter, hjradius]
        simp
    | succ k ih =>
        intro hk
        have hkCell : k < cellCount := by
          dsimp [knotCount, cellCount]
          omega
        let i : Fin cellCount := ⟨k, hkCell⟩
        let j₀ : Fin knotCount := ⟨k, by omega⟩
        let j₁ : Fin knotCount := ⟨k + 1, hk⟩
        have hprev := ih (by omega : k < knotCount)
        let start := sourcePartitionKnotIndex n upper lower k
        let stop := sourcePartitionKnotIndex n upper lower (k + 1)
        have hstart : AdditivePath.blockStart lengths i.val = start := by
          simpa [start, lengths, i] using
            blockStart_sourcePartitionCellStepLengths n upper lower i
        have hstartStop : start ≤ stop := by
          dsimp [start, stop]
          exact sourcePartitionKnotIndex_mono n upper lower (Nat.le_succ k)
        have hlength : lengths i.val = stop - start := by
          change sourcePartitionCellStepLengths n upper lower i.val = stop - start
          rw [sourcePartitionCellStepLengths_eq_floorDifference n upper lower i]
        have hstop : start + lengths i.val = stop := by
          rw [hlength]
          exact Nat.add_sub_of_le hstartStop
        have hprevPath :
            (scale n)⁻¹ * AdditivePath.displacement start increment ∈
              Set.Icc (center j₀ - radius j₀) (center j₀ + radius j₀) := by
          have hprev' := hprev
          rw [sourceNormalizedStepCadlagPathIcc_commonPartitionGrid_apply
            scale hn increment upper lower j₀] at hprev'
          simpa [j₀, start] using hprev'
        rcases hprevPath with ⟨hprevLower, hprevUpper⟩
        have hstartCoreLower : scale n * center j₀ - scale n * radius j₀ ≤
            AdditivePath.displacement start increment := by
          calc
            scale n * center j₀ - scale n * radius j₀ =
                scale n * (center j₀ - radius j₀) := by ring
            _ ≤ scale n * ((scale n)⁻¹ * AdditivePath.displacement start increment) :=
              mul_le_mul_of_nonneg_left hprevLower hscale.le
            _ = AdditivePath.displacement start increment := by
              rw [← mul_assoc, mul_inv_cancel₀ hscale.ne', one_mul]
        have hstartCoreUpper : AdditivePath.displacement start increment ≤
            scale n * center j₀ + scale n * radius j₀ := by
          calc
            AdditivePath.displacement start increment =
                scale n * ((scale n)⁻¹ * AdditivePath.displacement start increment) := by
              rw [← mul_assoc, mul_inv_cancel₀ hscale.ne', one_mul]
            _ ≤ scale n * (center j₀ + radius j₀) :=
              mul_le_mul_of_nonneg_left hprevUpper hscale.le
            _ = scale n * center j₀ + scale n * radius j₀ := by ring
        have hblock := hblocks i
        change partitionCellCoreReturnBlockEvent
          (scale n * innerLower i) (scale n * innerUpper i)
          (scale n * center j₀) (scale n * radius j₀)
          (scale n * center j₁) (scale n * radius j₁)
          (Combinatorics.Sequence.blockCoordinates (AdditivePath.blockStart lengths i.val)
            (lengths i.val) increment) at hblock
        have hradius : scale n * radius j₀ < scale n * radius j₁ := by
          exact mul_lt_mul_of_pos_left (hradiusStep i) hscale
        have hnextRaw := partitionCellCoreReturnBlockEvent_endpoint_mem
          hradius ⟨hstartCoreLower, hstartCoreUpper⟩ hblock
        have hpartial :
            Fin.partialSum
                (Combinatorics.Sequence.blockCoordinates
                  (AdditivePath.blockStart lengths i.val) (lengths i.val) increment)
                (Fin.last (lengths i.val)) =
              AdditivePath.blockSum start (lengths i.val) increment := by
          rw [partialSum_blockCoordinates]
          simp [hstart]
        have hdispStop :
            AdditivePath.displacement stop increment =
              AdditivePath.displacement start increment +
                Fin.partialSum
                  (Combinatorics.Sequence.blockCoordinates
                    (AdditivePath.blockStart lengths i.val) (lengths i.val) increment)
                  (Fin.last (lengths i.val)) := by
          rw [← hstop, AdditivePath.displacement_add_eq_add_blockSum, hpartial]
        have hnextRaw' :
            scale n * (center j₁ - radius j₁) < AdditivePath.displacement stop increment ∧
              AdditivePath.displacement stop increment <
                scale n * (center j₁ + radius j₁) := by
          rcases hnextRaw with ⟨hlo, hhi⟩
          constructor
          · calc
              scale n * (center j₁ - radius j₁) =
                  scale n * center j₁ - scale n * radius j₁ := by ring
              _ < AdditivePath.displacement start increment +
                  Fin.partialSum
                    (Combinatorics.Sequence.blockCoordinates
                      (AdditivePath.blockStart lengths i.val) (lengths i.val) increment)
                    (Fin.last (lengths i.val)) := hlo
              _ = AdditivePath.displacement stop increment := hdispStop.symm
          · calc
              AdditivePath.displacement stop increment =
                  AdditivePath.displacement start increment +
                    Fin.partialSum
                      (Combinatorics.Sequence.blockCoordinates
                        (AdditivePath.blockStart lengths i.val) (lengths i.val) increment)
                      (Fin.last (lengths i.val)) := hdispStop
              _ < scale n * center j₁ + scale n * radius j₁ := hhi
              _ = scale n * (center j₁ + radius j₁) := by ring
        have hnextLower : center j₁ - radius j₁ <
            (scale n)⁻¹ * AdditivePath.displacement stop increment := by
          have hraw : (center j₁ - radius j₁) * scale n <
              AdditivePath.displacement stop increment := by
            simpa [mul_comm] using hnextRaw'.1
          have h := (lt_div_iff₀ hscale).2 hraw
          simpa [div_eq_mul_inv, mul_comm] using h
        have hnextUpper : (scale n)⁻¹ * AdditivePath.displacement stop increment <
            center j₁ + radius j₁ := by
          have hraw : AdditivePath.displacement stop increment <
              (center j₁ + radius j₁) * scale n := by
            simpa [mul_comm] using hnextRaw'.2
          have h := (div_lt_iff₀ hscale).2 hraw
          simpa [div_eq_mul_inv, mul_comm] using h
        have hnextPath :
            sourceNormalizedStepCadlagPathIcc scale n increment
                (StepBoundary.commonPartitionGrid upper lower (k + 1)) =
              (scale n)⁻¹ * AdditivePath.displacement stop increment := by
          rw [sourceNormalizedStepCadlagPathIcc_commonPartitionGrid_apply
            scale hn increment upper lower j₁]
        rw [hnextPath]
        exact ⟨le_of_lt hnextLower, hnextUpper.le⟩
  intro j
  exact hcore j.val j.isLt


private theorem stepBoundary_eval_eq_rightTrace_of_mem_sourcePartitionCell
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

theorem sourceNormalizedStepCadlagPathIcc_mem_corridorSet_of_partitionCellCoreReturnBlockEvents
    {n : ℕ} {scale : ℕ → ℝ} (hn : 0 < n) (hscale : 0 < scale n)
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
          (AdditivePath.blockStart (sourcePartitionCellStepLengths n upper lower) i.val)
          (sourcePartitionCellStepLengths n upper lower i.val) increment ∈
        {block | partitionCellCoreReturnBlockEvent
          (scale n * innerLower i) (scale n * innerUpper i)
          (scale n * center (commonPartitionCellLeftKnotIndex upper lower i))
          (scale n * radius (commonPartitionCellLeftKnotIndex upper lower i))
          (scale n * center (commonPartitionCellRightKnotIndex upper lower i))
          (scale n * radius (commonPartitionCellRightKnotIndex upper lower i)) block}) :
    sourceNormalizedStepCadlagPathIcc scale n increment ∈
      Skorokhod.PathClass.StepCorridor.corridorSet upper lower := by
  let knotCount := (StepBoundary.commonKnots upper lower).card
  let lengths := sourcePartitionCellStepLengths n upper lower
  have hcore := sourceNormalizedStepCadlagPathIcc_commonPartitionGrid_mem_core_of_blockEvents
    hn hscale upper lower center radius innerLower innerUpper increment hcenter0 hradius0
    (by simpa [commonPartitionCellLeftKnotIndex, commonPartitionCellRightKnotIndex]
      using hradiusStep) (by
        intro i
        simpa [commonPartitionCellLeftKnotIndex, commonPartitionCellRightKnotIndex]
          using hblocks i)
  have hpathValue (t : unitInterval) (ht : t ≠ ⊤) :
      sourceNormalizedStepCadlagPathIcc scale n increment t =
        (scale n)⁻¹ * AdditivePath.displacement
          (commonPartitionFloorTimeIndex n t) increment := by
    rw [sourceNormalizedStepCadlagPathIcc_apply_of_ne_top scale n increment ht]
    rfl
  have hcoreRaw (j : Fin knotCount) :
      AdditivePath.displacement
          (sourcePartitionKnotIndex n upper lower j.val) increment ∈
        Set.Icc (scale n * center j - scale n * radius j)
          (scale n * center j + scale n * radius j) := by
    have hnormalized := hcore j
    rw [sourceNormalizedStepCadlagPathIcc_commonPartitionGrid_apply
      scale hn increment upper lower j] at hnormalized
    rcases hnormalized with ⟨hlo, hhi⟩
    constructor
    · calc
        scale n * center j - scale n * radius j =
            scale n * (center j - radius j) := by ring
        _ ≤ scale n * ((scale n)⁻¹ * AdditivePath.displacement
            (sourcePartitionKnotIndex n upper lower j.val) increment) :=
          mul_le_mul_of_nonneg_left hlo hscale.le
        _ = _ := by
          rw [← mul_assoc, mul_inv_cancel₀ hscale.ne', one_mul]
    · calc
        AdditivePath.displacement
            (sourcePartitionKnotIndex n upper lower j.val) increment =
            scale n * ((scale n)⁻¹ * AdditivePath.displacement
              (sourcePartitionKnotIndex n upper lower j.val) increment) := by
                rw [← mul_assoc, mul_inv_cancel₀ hscale.ne', one_mul]
        _ ≤ scale n * (center j + radius j) := mul_le_mul_of_nonneg_left hhi hscale.le
        _ = scale n * center j + scale n * radius j := by ring
  have knotCorridor (t : unitInterval) (ht : t ∈ StepBoundary.commonKnots upper lower) :
      lower.eval t <
          (sourceNormalizedStepCadlagPathIcc scale n increment t : EReal) ∧
        (sourceNormalizedStepCadlagPathIcc scale n increment t : EReal) <
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
        (sourceNormalizedStepCadlagPathIcc scale n increment
          (StepBoundary.commonPartitionGrid upper lower j.val) : EReal) :=
      EReal.coe_le_coe_iff.mpr hcore'.1
    have hpathCoreUpper :
        (sourceNormalizedStepCadlagPathIcc scale n increment
          (StepBoundary.commonPartitionGrid upper lower j.val) : EReal) ≤
          (center j + radius j : EReal) := EReal.coe_le_coe_iff.mpr hcore'.2
    constructor
    · calc
        lower.eval t = lower.rightTrace
            (StepBoundary.commonPartitionGrid upper lower j.val) := by
              rw [← hj, StepBoundary.rightTrace_eq_eval]
        _ < (center j - radius j : EReal) := hlowCore
        _ ≤ (sourceNormalizedStepCadlagPathIcc scale n increment
            (StepBoundary.commonPartitionGrid upper lower j.val) : EReal) := hpathCoreLower
        _ = _ := by rw [hj]
    · calc
        (sourceNormalizedStepCadlagPathIcc scale n increment t : EReal) =
            (sourceNormalizedStepCadlagPathIcc scale n increment
              (StepBoundary.commonPartitionGrid upper lower j.val) : EReal) := by rw [hj]
        _ ≤ (center j + radius j : EReal) := hpathCoreUpper
        _ < upper.rightTrace (StepBoundary.commonPartitionGrid upper lower j.val) := hupperCore
        _ = upper.eval t := by rw [← hj, StepBoundary.rightTrace_eq_eval]
  have hcorridor (t : unitInterval) :
      lower.eval t <
          (sourceNormalizedStepCadlagPathIcc scale n increment t : EReal) ∧
        (sourceNormalizedStepCadlagPathIcc scale n increment t : EReal) <
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
      let start := sourcePartitionKnotIndex n upper lower i.val
      let stop := sourcePartitionKnotIndex n upper lower (i.val + 1)
      let position := commonPartitionFloorTimeIndex n t
      have hleftTime : left ≤ t := hleftStrict.le
      have hrightTime : t ≤ right := hrightStrict.le
      have hstart_eq : AdditivePath.blockStart lengths i.val = start := by
        simpa [start, lengths] using
          blockStart_sourcePartitionCellStepLengths n upper lower i
      have hlength : lengths i.val = stop - start := by
        change sourcePartitionCellStepLengths n upper lower i.val = stop - start
        rw [sourcePartitionCellStepLengths_eq_floorDifference n upper lower i]
      have hstartPosition : start ≤ position := by
        have hstartIndex : start = commonPartitionFloorTimeIndex n left := by
          dsimp [start, left]
          exact sourcePartitionKnotIndex_eq_floor_of_lt_last n upper lower i.isLt
        rw [hstartIndex]
        exact commonPartitionFloorTimeIndex_mono n hleftTime
      have hpositionStop : position ≤ stop := by
        have hfloor : position ≤ commonPartitionFloorTimeIndex n right :=
          commonPartitionFloorTimeIndex_mono n hrightTime
        have hclip : position ≤ n - 1 :=
          commonPartitionFloorTimeIndex_le_n_sub_one_of_lt_top n
            (lt_of_lt_of_le hrightStrict le_top)
        dsimp [stop, sourcePartitionKnotIndex]
        exact le_min hfloor hclip
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
          (sourceNormalizedStepCadlagPathIcc scale n increment t : EReal) := by
        rw [hpathValue t httop]
        exact EReal.coe_lt_coe_iff.mpr hrealLower
      have hpathUpper :
          (sourceNormalizedStepCadlagPathIcc scale n increment t : EReal) <
            (innerUpper i : EReal) := by
        rw [hpathValue t httop]
        exact EReal.coe_lt_coe_iff.mpr hrealUpper
      have hlowerEval := stepBoundary_eval_eq_rightTrace_of_mem_sourcePartitionCell
        lower upper lower
        (fun q hq => StepBoundary.mem_commonKnots_of_mem_lower upper lower hq)
        i (by simpa [left] using hleftTime) (by simpa [right] using hrightStrict)
      have hupperEval := stepBoundary_eval_eq_rightTrace_of_mem_sourcePartitionCell
        upper upper lower
        (fun q hq => StepBoundary.mem_commonKnots_of_mem_upper upper lower hq)
        i (by simpa [left] using hleftTime) (by simpa [right] using hrightStrict)
      constructor
      · rw [hlowerEval]
        exact (hgeometry i).1.trans hpathLower
      · rw [hupperEval]
        exact hpathUpper.trans (hgeometry i).2
  change sourceNormalizedStepCadlagPathIcc scale n increment ⊥ = 0 ∧
    ∀ t, lower.eval t <
      (sourceNormalizedStepCadlagPathIcc scale n increment t : EReal) ∧
      (sourceNormalizedStepCadlagPathIcc scale n increment t : EReal) < upper.eval t
  exact ⟨by
    have hbotne : (⊥ : unitInterval) ≠ ⊤ := by norm_num [unitInterval]
    rw [sourceNormalizedStepCadlagPathIcc_apply_of_ne_top scale n increment hbotne]
    simp [RandomWalk.normalizedStepPath], hcorridor⟩


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

end

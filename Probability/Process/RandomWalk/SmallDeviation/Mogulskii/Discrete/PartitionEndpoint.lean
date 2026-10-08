/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Corridor.Measure
public import Probability.Process.RandomWalk.Path.Block.Law
public import Probability.Process.RandomWalk.Path.Cadlag
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.PartitionCorridor

/-!
# Endpoint-core events on discrete corridor cells

An incoming core contracts the cell corridor. A slightly wider outgoing core
is reached by an open endpoint band. These events depend only on the
increments in their own floor-rounded cell, so their probabilities factor
under an IID increment law.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.Process.SmallDeviation.Mogulskii

/-- The local event for one finite-partition cell. Relative partial sums stay
inside the corridor contracted by the incoming core; the endpoint band
connects the incoming core center to the outgoing core center. The band
radius is half the increase in core radius, matching the source lower
construction and leaving strict room inside the outgoing core. -/
def partitionCellCoreReturnBlockEvent {length : ℕ}
    (innerLower innerUpper startCenter startRadius endCenter endRadius : ℝ)
    (block : Fin length → ℝ) : Prop :=
  InOpenPartialSumCorridorEndsIn
    (innerLower + startRadius - startCenter)
    (innerUpper - startRadius - startCenter)
    (endCenter - startCenter - (endRadius - startRadius) / 2)
    (endCenter - startCenter + (endRadius - startRadius) / 2)
    block

/-- A finite endpoint-core cell event is measurable in the product sigma
algebra on its IID increment coordinates. -/
theorem measurableSet_partitionCellCoreReturnBlockEvent {length : ℕ}
    (innerLower innerUpper startCenter startRadius endCenter endRadius : ℝ) :
    MeasurableSet {block : Fin length → ℝ |
      partitionCellCoreReturnBlockEvent innerLower innerUpper startCenter
        startRadius endCenter endRadius block} := by
  exact measurableSet_inOpenPartialSumCorridorEndsIn _ _ _ _

/-- If the starting position is in the incoming core, every partial-sum
position of a core-return block lies in the prescribed inner cell corridor. -/
theorem partitionCellCoreReturnBlockEvent_positions_mem
    {length : ℕ} {innerLower innerUpper startCenter startRadius endCenter endRadius x : ℝ}
    {block : Fin length → ℝ}
    (hstart : x ∈ Set.Icc (startCenter - startRadius) (startCenter + startRadius))
    (hevent : partitionCellCoreReturnBlockEvent innerLower innerUpper startCenter
      startRadius endCenter endRadius block) :
    ∀ k : Fin (length + 1),
      innerLower < x + Fin.partialSum block k ∧
        x + Fin.partialSum block k < innerUpper := by
  intro k
  have hsum := hevent.1 k
  change innerLower + startRadius - startCenter < Fin.partialSum block k ∧
      Fin.partialSum block k < innerUpper - startRadius - startCenter at hsum
  constructor <;> nlinarith [hstart.1, hstart.2]

/-- The open endpoint band in a core-return block lands strictly inside the
outgoing core, uniformly over every starting point in the incoming core. -/
theorem partitionCellCoreReturnBlockEvent_endpoint_mem
    {length : ℕ} {innerLower innerUpper startCenter startRadius endCenter endRadius x : ℝ}
    {block : Fin length → ℝ}
    (hradius : startRadius < endRadius)
    (hstart : x ∈ Set.Icc (startCenter - startRadius) (startCenter + startRadius))
    (hevent : partitionCellCoreReturnBlockEvent innerLower innerUpper
      startCenter startRadius endCenter endRadius block) :
    x + Fin.partialSum block (Fin.last length) ∈
      Set.Ioo (endCenter - endRadius) (endCenter + endRadius) := by
  have hend := hevent.2
  change Fin.partialSum block (Fin.last length) ∈
    Set.Ioo (endCenter - startCenter - (endRadius - startRadius) / 2)
      (endCenter - startCenter + (endRadius - startRadius) / 2) at hend
  rcases hend with ⟨hendLower, hendUpper⟩
  rcases hstart with ⟨hstartLower, hstartUpper⟩
  constructor <;> nlinarith [hradius]

/-- The finite family of endpoint-core events on adjacent variable-length
IID increment blocks factors exactly into the corresponding one-cell
probabilities. -/
theorem iidSequenceLaw_forall_partitionCellCoreReturnBlockEvent_eq_prod
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (length : ℕ → ℕ) (blocks : ℕ)
    (innerLower innerUpper startCenter startRadius endCenter endRadius :
      Fin blocks → ℝ) :
    iidSequenceLaw ν {increment : ℕ → ℝ |
      ∀ i : Fin blocks,
        Combinatorics.Sequence.blockCoordinates
          (AdditivePath.blockStart length i.val) (length i.val) increment ∈
          {block | partitionCellCoreReturnBlockEvent
            (innerLower i) (innerUpper i) (startCenter i) (startRadius i)
            (endCenter i) (endRadius i) block}} =
      ∏ i : Fin blocks, iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 (length i.val) increment ∈
          {block | partitionCellCoreReturnBlockEvent
            (innerLower i) (innerUpper i) (startCenter i) (startRadius i)
      (endCenter i) (endRadius i) block}} := by
  exact iidSequenceLaw_measure_forall_variableConsecutiveBlockEvent
    ν length blocks
    (fun i => {block | partitionCellCoreReturnBlockEvent
      (innerLower i) (innerUpper i) (startCenter i) (startRadius i)
      (endCenter i) (endRadius i) block})
    (fun i => measurableSet_partitionCellCoreReturnBlockEvent
      (innerLower i) (innerUpper i) (startCenter i) (startRadius i)
      (endCenter i) (endRadius i))

theorem normalizedStepCadlagPathIcc_commonPartitionGrid_apply
    (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ)
    (upper lower : ProbabilityTheory.Process.SmallDeviation.Mogulskii.StepBoundary)
    (k : ℕ) :
    RandomWalk.normalizedStepCadlagPathIcc scale n increment
        (StepBoundary.commonPartitionGrid upper lower k) =
      (scale n)⁻¹ * AdditivePath.displacement
        (commonPartitionFloorTimeIndex n
          (StepBoundary.commonPartitionGrid upper lower k)) increment := by
  change RandomWalk.normalizedStepPath scale n increment
    (StepBoundary.commonPartitionGrid upper lower k : ℝ) = _
  rw [RandomWalk.normalizedStepPath]
  rfl

/-- The endpoint bands on the floor-rounded partition cells propagate the
normalized walk from the initial value zero into every prescribed knot core.
This is the discrete endpoint-core induction used by the lower corridor
bound. -/
theorem normalizedStepCadlagPathIcc_commonPartitionGrid_mem_core_of_blockEvents
    {n : ℕ} {scale : ℕ → ℝ} (hscale : 0 < scale n)
    (upper lower : ProbabilityTheory.Process.SmallDeviation.Mogulskii.StepBoundary)
    (center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ)
    (innerLower innerUpper :
      Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hcenter0 : ∀ j, j.val = 0 → center j = 0)
    (hradius0 : ∀ j, j.val = 0 → radius j = 0)
    (hradiusStep : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      radius ⟨i.val, by omega⟩ < radius ⟨i.val + 1, by omega⟩)
    (hblocks : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      Combinatorics.Sequence.blockCoordinates
          (AdditivePath.blockStart (commonPartitionCellStepLengths n upper lower) i.val)
          (commonPartitionCellStepLengths n upper lower i.val) increment ∈
        {block | partitionCellCoreReturnBlockEvent
          (scale n * innerLower i) (scale n * innerUpper i)
          (scale n * center ⟨i.val, by omega⟩)
          (scale n * radius ⟨i.val, by omega⟩)
          (scale n * center ⟨i.val + 1, by omega⟩)
          (scale n * radius ⟨i.val + 1, by omega⟩) block}) :
    ∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      RandomWalk.normalizedStepCadlagPathIcc scale n increment
          (StepBoundary.commonPartitionGrid upper lower j.val) ∈
        Set.Icc (center j - radius j) (center j + radius j) := by
  let knotCount := (StepBoundary.commonKnots upper lower).card
  let cellCount := knotCount - 1
  let lengths := commonPartitionCellStepLengths n upper lower
  have hcore : ∀ k : ℕ, (hk : k < knotCount) →
      RandomWalk.normalizedStepCadlagPathIcc scale n increment
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
        let start := commonPartitionFloorTimeIndex n
          (StepBoundary.commonPartitionGrid upper lower k)
        let stop := commonPartitionFloorTimeIndex n
          (StepBoundary.commonPartitionGrid upper lower (k + 1))
        have hstart : AdditivePath.blockStart lengths i.val = start := by
          simpa [start, lengths, i] using
            blockStart_commonPartitionCellStepLengths n upper lower i
        have hgridMono :
            StepBoundary.commonPartitionGrid upper lower k ≤
              StepBoundary.commonPartitionGrid upper lower (k + 1) :=
          StepBoundary.monotone_commonPartitionGrid upper lower (Nat.le_succ k)
        have hstartStop : start ≤ stop := by
          dsimp [start, stop]
          exact commonPartitionFloorTimeIndex_mono n hgridMono
        have hlength : lengths i.val = stop - start := by
          change (if h : i.val < (StepBoundary.commonKnots upper lower).card - 1 then
            commonPartitionFloorTimeIndex n
                (StepBoundary.commonPartitionGrid upper lower (i.val + 1)) -
              commonPartitionFloorTimeIndex n
                (StepBoundary.commonPartitionGrid upper lower i.val)
            else 0) = stop - start
          rw [dite_eq_left i.isLt]
        have hstop : start + lengths i.val = stop := by
          rw [hlength]
          exact Nat.add_sub_of_le hstartStop
        have hprevPath :
            (scale n)⁻¹ * AdditivePath.displacement start increment ∈
              Set.Icc (center j₀ - radius j₀) (center j₀ + radius j₀) := by
          have hprev' := hprev
          rw [normalizedStepCadlagPathIcc_commonPartitionGrid_apply] at hprev'
          simpa [j₀, start] using hprev'
        rcases hprevPath with ⟨hprevLower, hprevUpper⟩
        have hstartCoreLower : scale n * center j₀ - scale n * radius j₀ ≤
            AdditivePath.displacement start increment := by
          calc
            scale n * center j₀ - scale n * radius j₀ =
                scale n * (center j₀ - radius j₀) := by ring
            _ ≤
                scale n * ((scale n)⁻¹ * AdditivePath.displacement start increment) :=
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
          rw [← hstop, AdditivePath.displacement_add_eq_add_blockSum,
            hpartial]
        have hnextRaw' :
            scale n * (center j₁ - radius j₁) <
                AdditivePath.displacement stop increment ∧
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
          have hraw :
              (center j₁ - radius j₁) * scale n <
                AdditivePath.displacement stop increment := by
            simpa [mul_comm] using hnextRaw'.1
          have h := (lt_div_iff₀ hscale).2 hraw
          simpa [div_eq_mul_inv, mul_comm] using h
        have hnextUpper : (scale n)⁻¹ * AdditivePath.displacement stop increment <
            center j₁ + radius j₁ := by
          have hraw :
              AdditivePath.displacement stop increment <
                (center j₁ + radius j₁) * scale n := by
            simpa [mul_comm] using hnextRaw'.2
          have h := (div_lt_iff₀ hscale).2 hraw
          simpa [div_eq_mul_inv, mul_comm] using h
        have hnextPath :
            RandomWalk.normalizedStepCadlagPathIcc scale n increment
                (StepBoundary.commonPartitionGrid upper lower (k + 1)) =
              (scale n)⁻¹ * AdditivePath.displacement stop increment := by
          rw [normalizedStepCadlagPathIcc_commonPartitionGrid_apply]
        rw [hnextPath]
        exact ⟨le_of_lt hnextLower, hnextUpper.le⟩
  intro j
  exact hcore j.val j.isLt

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

end

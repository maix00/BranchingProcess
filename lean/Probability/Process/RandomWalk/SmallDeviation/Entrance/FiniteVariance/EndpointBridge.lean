/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Corridor.Comparison
public import Probability.Process.RandomWalk.SmallDeviation.Entrance.NormalDomain
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.RandomWalkBounds.Partition.Endpoint
/-!
# Entrance followed by a robust endpoint bridge

This file connects a finite-variance entrance event to a longer corridor
event.  The entrance endpoint is the source core of a robust bridge block;
the finite-block comparison theorem then multiplies the two probabilities.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

/-- An entrance block of width `D`, followed by a robust endpoint-core block,
produces a path that stays in `[-ratio * D, 0]` and ends in the final interval
`[-ratio * D, (-ratio + 1) * D]`.  The source core is the central third of the
entrance corridor. -/
theorem iidSequenceLaw_measure_mul_of_finiteMovingEntranceEvent_bridge
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (prefixLength bridgeLength : ℕ) (D ratio : ℝ)
    (hD : 0 < D) (hratio : 1 < ratio)
    (entryLower bridgeLower : ℝ≥0∞)
    (hentry : entryLower ≤ iidSequenceLaw ν
      {increment : ℕ → ℝ |
        finitePrefixVector (n := prefixLength) increment ∈
          finiteMovingEntranceEvent (n := prefixLength) D 0 1})
    (hbridge : bridgeLower ≤ iidSequenceLaw ν
      {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 bridgeLength increment ∈
          {block : Fin bridgeLength → ℝ |
            partitionCellCoreReturnBlockEvent
              (-ratio * D) 0 (-D / 2) (D / 6)
              ((-ratio + 1 / 2) * D) (D / 2) block}}) :
    bridgeLower * entryLower ≤ iidSequenceLaw ν
      {increment : ℕ → ℝ |
        InClosedInterval (-ratio * D) 0 (prefixLength + bridgeLength) 0 increment ∧
        AdditivePath.displacement (prefixLength + bridgeLength) increment ∈
          Set.Icc (-ratio * D) ((-ratio + 1) * D)} := by
  classical
  let entrance : Set (Fin prefixLength → ℝ) :=
    finiteMovingEntranceEvent (n := prefixLength) D 0 1
  let bridge : Set (Fin bridgeLength → ℝ) :=
    {block | partitionCellCoreReturnBlockEvent
      (-ratio * D) 0 (-D / 2) (D / 6)
      ((-ratio + 1 / 2) * D) (D / 2) block}
  let entranceSequence : Set (ℕ → ℝ) :=
    {increment | Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈
      entrance}
  let target : Set (ℕ → ℝ) :=
    {increment |
      InClosedInterval (-ratio * D) 0 (prefixLength + bridgeLength) 0 increment ∧
      AdditivePath.displacement (prefixLength + bridgeLength) increment ∈
        Set.Icc (-ratio * D) ((-ratio + 1) * D)}
  have hentranceMeasurable : MeasurableSet entrance := by
    have hsafe := measurableSet_finiteDriftRemovedOffsetCorridorEvent
      (n := prefixLength) D 0 1
    have hevent : finiteDriftRemovedOffsetCorridorEvent
        (n := prefixLength) D 0 1 = entrance := by
      ext x
      exact finiteDriftRemovedOffsetCorridorEvent_iff_finiteMovingEntranceEvent
        D 0 1 x
    rw [← hevent]
    exact hsafe
  have hbridgeMeasurable : MeasurableSet bridge :=
    measurableSet_partitionCellCoreReturnBlockEvent
      (-ratio * D) 0 (-D / 2) (D / 6)
      ((-ratio + 1 / 2) * D) (D / 2)
  have hentrySequence : entryLower ≤ iidSequenceLaw ν entranceSequence := by
    have hset : entranceSequence =
        {increment : ℕ → ℝ |
          finitePrefixVector (n := prefixLength) increment ∈ entrance} := by
      ext increment
      change Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈ entrance ↔
        finitePrefixVector (n := prefixLength) increment ∈ entrance
      have heq : Combinatorics.Sequence.blockCoordinates 0 prefixLength increment =
          finitePrefixVector (n := prefixLength) increment := by
        funext i
        simp [Combinatorics.Sequence.blockCoordinates, finitePrefixVector]
      rw [heq]
    rw [hset]
    simpa [entrance] using hentry
  have hbridgeGeometry (increment : ℕ → ℝ)
      (hfirst : Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈
        entrance)
      (hnext : Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength
        increment ∈ bridge) : increment ∈ target := by
    have hfirstPath (j : Fin (prefixLength + 1)) :
        AdditivePath.displacement j.val increment ∈ Set.Icc (-D) 0 := by
      have hsum : Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment) j =
          AdditivePath.displacement j.val increment := by
        rw [partialSum_blockCoordinates, AdditivePath.blockSum_zero_start]
      have hraw : finiteNormalizedStepKnots D
          (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment) j ∈
            Set.Icc (-1) 0 := by
        simpa [finiteMovingEntranceEvent] using hfirst.1 j
      rw [finiteNormalizedStepKnots, hsum] at hraw
      rcases Set.mem_Icc.mp hraw with ⟨hlo, hhi⟩
      have hmul : D * (D⁻¹ * AdditivePath.displacement j.val increment) =
          AdditivePath.displacement j.val increment := by
        field_simp [hD.ne']
      constructor
      · have := mul_le_mul_of_nonneg_left hlo hD.le
        rw [hmul] at this
        nlinarith
      · have := mul_le_mul_of_nonneg_left hhi hD.le
        rw [hmul] at this
        nlinarith
    have hendpointRaw :
        finiteNormalizedStepKnots D
          (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment)
          (Fin.last prefixLength) ∈ Set.Icc (-(2 / 3 : ℝ)) (-(1 / 3 : ℝ)) := by
      have hend := hfirst.2
      change (1 / 3 - 1 + 0 * (prefixLength : ℝ) ≤
          finiteNormalizedStepKnots D
            (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment)
            (Fin.last prefixLength)) ∧
        finiteNormalizedStepKnots D
            (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment)
            (Fin.last prefixLength) ≤ 2 / 3 - 1 + 0 * (prefixLength : ℝ) at hend
      rcases hend with ⟨hlo, hhi⟩
      constructor <;> nlinarith
    have hsumLast : Fin.partialSum
        (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment)
        (Fin.last prefixLength) = AdditivePath.displacement prefixLength increment := by
      simpa [partialSum_blockCoordinates, AdditivePath.blockSum_zero_start]
    rw [finiteNormalizedStepKnots, hsumLast] at hendpointRaw
    have hendpoint : AdditivePath.displacement prefixLength increment ∈
        Set.Icc (-2 * D / 3) (-D / 3) := by
      rcases Set.mem_Icc.mp hendpointRaw with ⟨hlo, hhi⟩
      have hmul : D * (D⁻¹ * AdditivePath.displacement prefixLength increment) =
          AdditivePath.displacement prefixLength increment := by
        field_simp [hD.ne']
      constructor
      · have := mul_le_mul_of_nonneg_left hlo hD.le
        rw [hmul] at this
        nlinarith
      · have := mul_le_mul_of_nonneg_left hhi hD.le
        rw [hmul] at this
        nlinarith
    have hsourceCore : AdditivePath.displacement prefixLength increment ∈
        Set.Icc ((-D / 2) - D / 6) ((-D / 2) + D / 6) := by
      rcases hendpoint with ⟨hlo, hhi⟩
      constructor <;> nlinarith
    have hblock : partitionCellCoreReturnBlockEvent
        (-ratio * D) 0 (-D / 2) (D / 6)
        ((-ratio + 1 / 2) * D) (D / 2)
        (Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength increment) :=
      hnext
    have hpositions := partitionCellCoreReturnBlockEvent_positions_mem
      (x := AdditivePath.displacement prefixLength increment)
      hsourceCore hblock
    have hpartial (j : Fin (bridgeLength + 1)) :
        Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength increment) j =
          AdditivePath.blockSum prefixLength j.val increment := by
      simp [partialSum_blockCoordinates, AdditivePath.blockSum_zero_start]
    have hglobal (j : Fin (bridgeLength + 1)) :
        AdditivePath.displacement (prefixLength + j.val) increment =
          AdditivePath.displacement prefixLength increment +
            Fin.partialSum
              (Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength increment) j := by
      rw [AdditivePath.displacement_add_eq_add_blockSum, hpartial]
    have hpath : InClosedInterval (-ratio * D) 0
        (prefixLength + bridgeLength) 0 increment := by
      change ∀ k : Fin (prefixLength + bridgeLength + 1),
        history (prefixLength + bridgeLength) 0 increment k ∈
          Set.Icc (-ratio * D) 0
      intro k
      rw [history_eq_fromIncrements]
      simp only [AdditivePath.fromIncrements, zero_add]
      by_cases hk : k.val ≤ prefixLength
      · let j : Fin (prefixLength + 1) := ⟨k.val, by omega⟩
        have hj := hfirstPath j
        have hlower : -ratio * D ≤ -D := by nlinarith [hratio, hD]
        have hjval : j.val = k.val := by simp [j]
        rw [hjval] at hj
        have hj' : AdditivePath.displacement k.val increment ∈ Set.Icc (-D) 0 := by
          exact hj
        exact ⟨hlower.trans hj'.1, hj'.2⟩
      · let j : Fin (bridgeLength + 1) :=
          ⟨k.val - prefixLength, by omega⟩
        have hindex : k.val = prefixLength + j.val := by
          dsimp [j]
          omega
        rw [hindex, hglobal j]
        have hpos := hpositions j
        rcases hpos with ⟨hlo, hhi⟩
        constructor
        · exact le_of_lt hlo
        · exact le_of_lt hhi
    have hradius : D / 6 < D / 2 := by linarith
    have hendCore := partitionCellCoreReturnBlockEvent_endpoint_mem
      (x := AdditivePath.displacement prefixLength increment)
      hradius hsourceCore hblock
    have hlast : AdditivePath.displacement (prefixLength + bridgeLength) increment =
        AdditivePath.displacement prefixLength increment +
          Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength increment)
            (Fin.last bridgeLength) := by
      simpa using hglobal (Fin.last bridgeLength)
    rw [← hlast] at hendCore
    have hend : AdditivePath.displacement (prefixLength + bridgeLength) increment ∈
        Set.Icc (-ratio * D) ((-ratio + 1) * D) := by
      rcases hendCore with ⟨hlo, hhi⟩
      constructor
      · have heq : (-ratio + 1 / 2) * D - D / 2 = -ratio * D := by ring
        rw [heq] at hlo
        exact le_of_lt hlo
      · have heq : (-ratio + 1 / 2) * D + D / 2 = (-ratio + 1) * D := by ring
        rw [heq] at hhi
        exact le_of_lt hhi
    exact ⟨hpath, hend⟩
  have hcomparison := iidSequenceLaw_measure_mul_le_card_mul_of_finite_block_cover
    ν (F := {()}) (prefixLength := prefixLength)
    (bridgeLength := bridgeLength) entranceSequence target
    (fun _ : Unit => entrance) (fun _ : Unit => bridge) bridgeLower
    (by intro i hi; exact hentranceMeasurable)
    (by intro i hi; exact hbridgeMeasurable)
    (by
      intro increment hincrement
      simpa [entranceSequence] using hincrement)
    (by intro i hi; simpa [bridge] using hbridge)
    (by
      intro i hi increment hevents
      apply hbridgeGeometry increment
      · simpa [entrance] using hevents.1
      · simpa [bridge] using hevents.2)
  have hcomparison' : bridgeLower * iidSequenceLaw ν entranceSequence ≤
      iidSequenceLaw ν target := by
    simpa [target] using hcomparison
  calc
    bridgeLower * entryLower = entryLower * bridgeLower := mul_comm _ _
    _ ≤ iidSequenceLaw ν entranceSequence * bridgeLower :=
      mul_le_mul_left hentrySequence _
    _ = bridgeLower * iidSequenceLaw ν entranceSequence := mul_comm _ _
    _ ≤ iidSequenceLaw ν target := hcomparison'

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end

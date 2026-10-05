/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Law.Coordinates
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurable excursion events of disjoint increment blocks

The prefix event for a block of length `m` observes sums of its first
`1, ..., m` increments. Consecutive blocks use disjoint coordinates, including
their common path endpoint only as a time, not as a shared increment.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- The partial sum through the `k`-th increment of a finite coordinate
block. The zero extension is used only to present the finite vector as an
ordinary increment sequence for `AdditivePath.displacement`. -/
def blockPrefixSum {length : ℕ} (coordinates : Fin length → ℝ)
    (k : Fin length) : ℝ :=
  AdditivePath.displacement (k.val + 1) (fun i =>
    if hi : i < length then coordinates ⟨i, hi⟩ else 0)

/-- A block crosses `threshold` if one of its nonempty initial partial sums
has absolute value at least `threshold`. -/
def blockPrefixExceedance (start length : ℕ) (threshold : ℝ) : Set (ℕ → ℝ) :=
  {path | ∃ k : Fin length,
    threshold ≤ |AdditivePath.blockSum start (k.val + 1) path|}

/-- The same excursion event expressed on the finite vector of increments in
one block. -/
def blockPrefixExceedanceOnCoordinates (length : ℕ) (threshold : ℝ) :
    Set (Fin length → ℝ) :=
  {coordinates | ∃ k : Fin length,
    threshold ≤ |blockPrefixSum coordinates k|}

theorem measurable_blockPrefixSum {length : ℕ} (k : Fin length) :
    Measurable (fun coordinates : Fin length → ℝ => blockPrefixSum coordinates k) := by
  unfold blockPrefixSum AdditivePath.displacement
  fun_prop

/-- The excursion event on a finite block is Borel measurable. -/
theorem measurableSet_blockPrefixExceedanceOnCoordinates
    (length : ℕ) (threshold : ℝ) :
    MeasurableSet (blockPrefixExceedanceOnCoordinates length threshold) := by
  rw [show blockPrefixExceedanceOnCoordinates length threshold =
      ⋃ k : Fin length, {coordinates | threshold ≤ |blockPrefixSum coordinates k|} by
    ext coordinates
    simp [blockPrefixExceedanceOnCoordinates]]
  exact MeasurableSet.iUnion fun k =>
    measurableSet_le measurable_const
      (continuous_abs.measurable.comp (measurable_blockPrefixSum k))

theorem blockPrefixSum_blockCoordinates
    (start length : ℕ) (path : ℕ → ℝ) (k : Fin length) :
    blockPrefixSum (AdditivePath.blockCoordinates start length path) k =
      AdditivePath.blockSum start (k.val + 1) path := by
  rw [blockPrefixSum, AdditivePath.blockSum_eq_displacement_natAdd]
  unfold AdditivePath.displacement
  apply Finset.sum_congr rfl
  intro i hi
  have hiLength : i < length := by
    have hik : i < k.val + 1 := Finset.mem_range.mp hi
    omega
  simp [AdditivePath.blockCoordinates, hiLength]

theorem blockPrefixExceedance_eq_preimage_blockCoordinates
    (start length : ℕ) (threshold : ℝ) :
    AdditivePath.blockCoordinates (E := ℝ) start length ⁻¹'
        blockPrefixExceedanceOnCoordinates length threshold =
      blockPrefixExceedance start length threshold := by
  ext path
  simp only [Set.mem_preimage, blockPrefixExceedanceOnCoordinates,
    blockPrefixExceedance, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by
    simpa [blockPrefixSum_blockCoordinates] using hk⟩

/-- Excursions in two consecutive coordinate blocks are independent under the
canonical IID path law. Each event uses exactly `length` increments, so the
two blocks are disjoint. -/
theorem measure_inter_adjacentBlockPrefixExceedance_eq_mul
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ) (leftThreshold rightThreshold : ℝ) :
    (iidSequenceLaw ν)
        (blockPrefixExceedance start length leftThreshold ∩
          blockPrefixExceedance (start + length) length rightThreshold) =
      (iidSequenceLaw ν) (blockPrefixExceedance start length leftThreshold) *
        (iidSequenceLaw ν) (blockPrefixExceedance (start + length) length rightThreshold) := by
  let leftEvent := blockPrefixExceedanceOnCoordinates length leftThreshold
  let rightEvent := blockPrefixExceedanceOnCoordinates length rightThreshold
  have hleft : MeasurableSet leftEvent :=
    measurableSet_blockPrefixExceedanceOnCoordinates length leftThreshold
  have hright : MeasurableSet rightEvent :=
    measurableSet_blockPrefixExceedanceOnCoordinates length rightThreshold
  have hindep := indepFun_blockCoordinates_blockCoordinates ν start length length
  have hfactor := hindep.measure_inter_preimage_eq_mul leftEvent rightEvent hleft hright
  dsimp [leftEvent, rightEvent] at hfactor
  rw [blockPrefixExceedance_eq_preimage_blockCoordinates start length leftThreshold,
    blockPrefixExceedance_eq_preimage_blockCoordinates
      (start + length) length rightThreshold] at hfactor
  exact hfactor

end ProbabilityTheory.RandomWalk

end

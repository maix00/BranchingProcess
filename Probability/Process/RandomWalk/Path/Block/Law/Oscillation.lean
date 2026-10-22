/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Oscillation
public import Probability.Process.RandomWalk.Path.Block.Law.Basic
public import Probability.Process.RandomWalk.Path.Block.Partition.Basic
public import Probability.Process.RandomWalk.Path.Event.Oscillation

/-!
# IID laws of finite-block oscillation events

For an IID increment sequence, the law of a finite block's partial-sum
oscillation event agrees with the corresponding range event of the full walk.
The prefix version observes the positions before the terminal increment, so
that last increment has no constraint.

The public declarations identify the IID probabilities of the strict full
block and half-open prefix events with `partialSumRangeOscillationLTProbability`.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- The one-block strict oscillation probability is the translation-invariant
partial-sum range probability over the same number of increments. -/
theorem iidSequenceLaw_blockOscillationLTEvent_eq_partialSumRangeProbability
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (width : ℝ) (length : ℕ) :
    iidSequenceLaw ν {increment : ℕ → ℝ |
      blockOscillationLTEvent width length
        (Combinatorics.Sequence.blockCoordinates 0 length increment)} =
      partialSumRangeOscillationLTProbability (iidSequenceLaw ν) width length := by
  change iidSequenceLaw ν
      {increment : ℕ → ℝ |
        blockOscillationLTEvent width length
          (Combinatorics.Sequence.blockCoordinates 0 length increment)} =
    iidSequenceLaw ν (partialSumRangeOscillationLTEvent width length)
  congr 1
  ext increment
  change (∀ i j : Fin (length + 1),
      |Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 length increment) i -
        Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 length increment) j| < width) ↔
    (∀ i j : Fin (length + 1),
      |AdditivePath.displacement (i : ℕ) increment -
        AdditivePath.displacement (j : ℕ) increment| < width)
  constructor <;> intro h i j
  · have hi : Fin.partialSum
        (Combinatorics.Sequence.blockCoordinates 0 length increment) i =
        AdditivePath.displacement (i : ℕ) increment := by
      rw [partialSum_blockCoordinates, AdditivePath.blockSum_zero_start]
    have hj : Fin.partialSum
        (Combinatorics.Sequence.blockCoordinates 0 length increment) j =
        AdditivePath.displacement (j : ℕ) increment := by
      rw [partialSum_blockCoordinates, AdditivePath.blockSum_zero_start]
    simpa [hi, hj] using h i j
  · have hi : Fin.partialSum
        (Combinatorics.Sequence.blockCoordinates 0 length increment) i =
        AdditivePath.displacement (i : ℕ) increment := by
      rw [partialSum_blockCoordinates, AdditivePath.blockSum_zero_start]
    have hj : Fin.partialSum
        (Combinatorics.Sequence.blockCoordinates 0 length increment) j =
        AdditivePath.displacement (j : ℕ) increment := by
      rw [partialSum_blockCoordinates, AdditivePath.blockSum_zero_start]
    simpa [hi, hj] using h i j

/-- The probability of the prefix oscillation event on a length-`m+1` block
is the range probability through time `m`. The last increment is unrestricted,
which matches the half-open partition-cell convention. -/
theorem iidSequenceLaw_blockOscillationPrefixLTEvent_eq_partialSumRangeProbability
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {width : ℝ} {length : ℕ} (hlength : 0 < length) :
    iidSequenceLaw ν {increment : ℕ → ℝ |
      blockOscillationPrefixLTEvent width length
        (Combinatorics.Sequence.blockCoordinates 0 length increment)} =
      partialSumRangeOscillationLTProbability (iidSequenceLaw ν) width (length - 1) := by
  have hpred : length - 1 + 1 = length := Nat.sub_add_cancel (by omega)
  change iidSequenceLaw ν
      {increment : ℕ → ℝ |
        ∀ i j : Fin length,
          |Fin.partialSum
              (Combinatorics.Sequence.blockCoordinates 0 length increment)
              i.castSucc -
            Fin.partialSum
              (Combinatorics.Sequence.blockCoordinates 0 length increment)
              j.castSucc| < width} =
    iidSequenceLaw ν (partialSumRangeOscillationLTEvent width (length - 1))
  rw [partialSumRangeOscillationLTEvent, hpred]
  congr 1
  ext increment
  have hvalue (i : Fin length) :
      Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 length increment)
          i.castSucc = AdditivePath.displacement (i : ℕ) increment := by
    rw [partialSum_blockCoordinates, AdditivePath.blockSum_zero_start]
    simp only [Fin.val_castSucc]
  simp only [Set.mem_ofPred_eq]
  simp only [hvalue]

end ProbabilityTheory.RandomWalk

end

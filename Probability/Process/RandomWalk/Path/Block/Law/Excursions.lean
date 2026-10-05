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

/-- Excursions in consecutive blocks remain independent when the two blocks
have different lengths. This is the event-level form of the variable-length
coordinate-block independence theorem. -/
theorem measure_inter_adjacentBlockPrefixExceedance_eq_mul_of_lengths
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start leftLength rightLength : ℕ) (leftThreshold rightThreshold : ℝ) :
    (iidSequenceLaw ν)
        (blockPrefixExceedance start leftLength leftThreshold ∩
          blockPrefixExceedance (start + leftLength) rightLength rightThreshold) =
      (iidSequenceLaw ν) (blockPrefixExceedance start leftLength leftThreshold) *
        (iidSequenceLaw ν)
          (blockPrefixExceedance (start + leftLength) rightLength rightThreshold) := by
  let leftEvent := blockPrefixExceedanceOnCoordinates leftLength leftThreshold
  let rightEvent := blockPrefixExceedanceOnCoordinates rightLength rightThreshold
  have hleft : MeasurableSet leftEvent :=
    measurableSet_blockPrefixExceedanceOnCoordinates leftLength leftThreshold
  have hright : MeasurableSet rightEvent :=
    measurableSet_blockPrefixExceedanceOnCoordinates rightLength rightThreshold
  have hindep := indepFun_blockCoordinates_blockCoordinates ν start leftLength rightLength
  have hfactor := hindep.measure_inter_preimage_eq_mul leftEvent rightEvent hleft hright
  dsimp [leftEvent, rightEvent] at hfactor
  rw [blockPrefixExceedance_eq_preimage_blockCoordinates start leftLength leftThreshold,
    blockPrefixExceedance_eq_preimage_blockCoordinates
      (start + leftLength) rightLength rightThreshold] at hfactor
  exact hfactor

/-- A finite-prefix excursion has the same probability after translating its
increment window by an arbitrary deterministic amount along an IID sequence. -/
theorem measure_blockPrefixExceedance_translate_eq
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (shift start length : ℕ) (threshold : ℝ) :
    (iidSequenceLaw ν) (blockPrefixExceedance (shift + start) length threshold) =
      (iidSequenceLaw ν) (blockPrefixExceedance start length threshold) := by
  let μ := iidSequenceLaw ν
  have hlarge : MeasurableSet (blockPrefixExceedance start length threshold) := by
    rw [← blockPrefixExceedance_eq_preimage_blockCoordinates]
    exact MeasurableSet.preimage
      (measurableSet_blockPrefixExceedanceOnCoordinates length threshold)
      (blockCoordinates_measurable start length)
  have hshift : Measurable ((fun path : ℕ → ℝ => fun k => path (shift + k))) :=
    measurable_natAdd shift
  have hshiftLaw := iidSequenceLaw_map_natAdd ν shift
  have hshiftEvent :
      (fun path : ℕ → ℝ => fun k => path (shift + k)) ⁻¹'
        blockPrefixExceedance start length threshold =
      blockPrefixExceedance (shift + start) length threshold := by
    ext path
    simp only [Set.mem_preimage, blockPrefixExceedance, Set.mem_ofPred_eq]
    constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by
      simpa [AdditivePath.blockSum_eq_displacement_natAdd,
        AdditivePath.displacement, Nat.add_assoc] using hk⟩
  calc
    μ (blockPrefixExceedance (shift + start) length threshold) =
        μ ((fun path : ℕ → ℝ => fun k => path (shift + k)) ⁻¹'
          blockPrefixExceedance start length threshold) := by rw [hshiftEvent]
    _ = (μ.map (fun path : ℕ → ℝ => fun k => path (shift + k)))
        (blockPrefixExceedance start length threshold) := by
          rw [Measure.map_apply hshift hlarge]
    _ = _ := by rw [hshiftLaw]

/-- Probability bounds on each of two independent adjacent-block events
multiply to a bound on their intersection. -/
theorem measure_inter_adjacentBlockPrefixExceedance_le_mul_of_bounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ) (leftThreshold rightThreshold : ℝ)
    (leftBound rightBound : ENNReal)
    (hleft : (iidSequenceLaw ν)
      (blockPrefixExceedance start length leftThreshold) ≤ leftBound)
    (hright : (iidSequenceLaw ν)
      (blockPrefixExceedance (start + length) length rightThreshold) ≤ rightBound) :
    (iidSequenceLaw ν)
      (blockPrefixExceedance start length leftThreshold ∩
        blockPrefixExceedance (start + length) length rightThreshold) ≤
      leftBound * rightBound := by
  rw [measure_inter_adjacentBlockPrefixExceedance_eq_mul]
  exact mul_le_mul hleft hright (by positivity) (by positivity)

/-- Separate bounds on adjacent excursion probabilities multiply even when
the two consecutive blocks have different lengths. -/
theorem measure_inter_adjacentBlockPrefixExceedance_le_mul_of_bounds_of_lengths
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start leftLength rightLength : ℕ) (leftThreshold rightThreshold : ℝ)
    (leftBound rightBound : ENNReal)
    (hleft : (iidSequenceLaw ν)
      (blockPrefixExceedance start leftLength leftThreshold) ≤ leftBound)
    (hright : (iidSequenceLaw ν)
      (blockPrefixExceedance (start + leftLength) rightLength rightThreshold) ≤ rightBound) :
    (iidSequenceLaw ν)
      (blockPrefixExceedance start leftLength leftThreshold ∩
        blockPrefixExceedance (start + leftLength) rightLength rightThreshold) ≤
      leftBound * rightBound := by
  rw [measure_inter_adjacentBlockPrefixExceedance_eq_mul_of_lengths]
  exact mul_le_mul hleft hright (by positivity) (by positivity)

/-- A common one-block probability bound gives its square for two adjacent
excursion events under the same IID sequence law. -/
theorem measure_inter_adjacentBlockPrefixExceedance_le_sq_of_bound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ) (threshold : ℝ) (bound : ENNReal)
    (hbound : (iidSequenceLaw ν)
      (blockPrefixExceedance start length threshold) ≤ bound) :
    (iidSequenceLaw ν)
      (blockPrefixExceedance start length threshold ∩
        blockPrefixExceedance (start + length) length threshold) ≤ bound ^ 2 := by
  have hright : (iidSequenceLaw ν)
      (blockPrefixExceedance (start + length) length threshold) ≤ bound := by
    calc
      _ = (iidSequenceLaw ν)
          (blockPrefixExceedance (length + start) length threshold) := by
            rw [Nat.add_comm]
      _ = (iidSequenceLaw ν) (blockPrefixExceedance start length threshold) :=
        measure_blockPrefixExceedance_translate_eq ν length start length threshold
      _ ≤ bound := hbound
  calc
    _ ≤ bound * bound :=
      measure_inter_adjacentBlockPrefixExceedance_le_mul_of_bounds ν start length
        threshold threshold bound bound hbound hright
    _ = bound ^ 2 := by rw [pow_two]

/-- A common one-block bound controls the union of adjacent-block excursion
pairs by the sum of their squared bounds. -/
theorem measure_iUnion_adjacentBlockPrefixExceedance_le_of_commonBound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {count : ℕ} (start : Fin count → ℕ) (length : ℕ)
    (threshold : ℝ) (bound : ENNReal)
    (hbound : ∀ j, (iidSequenceLaw ν)
      (blockPrefixExceedance (start j) length threshold) ≤ bound) :
    (iidSequenceLaw ν)
      (⋃ j : Fin count,
        blockPrefixExceedance (start j) length threshold ∩
          blockPrefixExceedance (start j + length) length threshold) ≤
      (count : ENNReal) * bound ^ 2 := by
  let pairEvent : Fin count → Set (ℕ → ℝ) := fun j =>
    blockPrefixExceedance (start j) length threshold ∩
      blockPrefixExceedance (start j + length) length threshold
  have hpair (j : Fin count) : (iidSequenceLaw ν) (pairEvent j) ≤ bound ^ 2 := by
    exact measure_inter_adjacentBlockPrefixExceedance_le_sq_of_bound ν
      (start j) length threshold bound (hbound j)
  calc
    (iidSequenceLaw ν) (⋃ j : Fin count, pairEvent j) ≤
        ∑' j : Fin count, (iidSequenceLaw ν) (pairEvent j) := measure_iUnion_le _
    _ = ∑ j : Fin count, (iidSequenceLaw ν) (pairEvent j) := by
      simp only [tsum_fintype]
    _ ≤ ∑ j : Fin count, bound ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      exact hpair j
    _ = (count : ENNReal) * bound ^ 2 := by simp

/-- A finite union of adjacent excursion pairs with varying block lengths is
bounded by the sum of the products of the corresponding one-block bounds. -/
theorem measure_iUnion_adjacentBlockPrefixExceedance_le_of_bounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {count : ℕ} (start leftLength rightLength : Fin count → ℕ)
    (leftThreshold rightThreshold : ℝ)
    (leftBound rightBound : Fin count → ENNReal)
    (hleft : ∀ j, (iidSequenceLaw ν)
      (blockPrefixExceedance (start j) (leftLength j) leftThreshold) ≤ leftBound j)
    (hright : ∀ j, (iidSequenceLaw ν)
      (blockPrefixExceedance (start j + leftLength j) (rightLength j)
        rightThreshold) ≤ rightBound j) :
    (iidSequenceLaw ν)
      (⋃ j : Fin count,
        blockPrefixExceedance (start j) (leftLength j) leftThreshold ∩
          blockPrefixExceedance (start j + leftLength j) (rightLength j)
            rightThreshold) ≤
      ∑ j : Fin count, leftBound j * rightBound j := by
  let pairEvent : Fin count → Set (ℕ → ℝ) := fun j =>
    blockPrefixExceedance (start j) (leftLength j) leftThreshold ∩
      blockPrefixExceedance (start j + leftLength j) (rightLength j)
        rightThreshold
  have hpair (j : Fin count) : (iidSequenceLaw ν) (pairEvent j) ≤
      leftBound j * rightBound j := by
    exact measure_inter_adjacentBlockPrefixExceedance_le_mul_of_bounds_of_lengths ν
      (start j) (leftLength j) (rightLength j) leftThreshold rightThreshold
      (leftBound j) (rightBound j) (hleft j) (hright j)
  calc
    (iidSequenceLaw ν) (⋃ j : Fin count, pairEvent j) ≤
        ∑' j : Fin count, (iidSequenceLaw ν) (pairEvent j) := measure_iUnion_le _
    _ = ∑ j : Fin count, (iidSequenceLaw ν) (pairEvent j) := by
      simp only [tsum_fintype]
    _ ≤ ∑ j : Fin count, leftBound j * rightBound j := by
      apply Finset.sum_le_sum
      intro j hj
      exact hpair j

/-- Eventual one-block bounds on each side of every pair yield the finite
union estimate for a varying adjacent-block grid. -/
theorem eventually_measure_iUnion_adjacentBlockPrefixExceedance_le_of_eventually_bounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {count : ℕ} (start leftLength rightLength : ℕ → Fin count → ℕ)
    (leftThreshold rightThreshold : ℕ → ℝ)
    (leftBound rightBound : ℕ → Fin count → ENNReal)
    (hleft : ∀ᶠ n in atTop, ∀ j,
      (iidSequenceLaw ν)
        (blockPrefixExceedance (start n j) (leftLength n j)
          (leftThreshold n)) ≤ leftBound n j)
    (hright : ∀ᶠ n in atTop, ∀ j,
      (iidSequenceLaw ν)
        (blockPrefixExceedance (start n j + leftLength n j) (rightLength n j)
          (rightThreshold n)) ≤ rightBound n j) :
    ∀ᶠ n in atTop,
      (iidSequenceLaw ν)
        (⋃ j : Fin count,
          blockPrefixExceedance (start n j) (leftLength n j)
              (leftThreshold n) ∩
            blockPrefixExceedance (start n j + leftLength n j)
              (rightLength n j) (rightThreshold n)) ≤
        ∑ j : Fin count, leftBound n j * rightBound n j := by
  filter_upwards [hleft, hright] with n hleftN hrightN
  exact measure_iUnion_adjacentBlockPrefixExceedance_le_of_bounds ν
    (start n) (leftLength n) (rightLength n) (leftThreshold n) (rightThreshold n)
    (leftBound n) (rightBound n) (hleftN) (hrightN)

/-- A one-block probability estimate that holds eventually along a sequence
of block lengths and thresholds yields the corresponding squared estimate for
two adjacent blocks. -/
theorem eventually_measure_inter_adjacentBlockPrefixExceedance_le_sq_of_oneBlockBound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ → ℕ) (threshold : ℕ → ℝ) (bound : ℕ → ENNReal)
    (hbound : ∀ᶠ n : ℕ in atTop,
      (iidSequenceLaw ν)
        (blockPrefixExceedance (start n) (length n) (threshold n)) ≤ bound n) :
    ∀ᶠ n : ℕ in atTop,
      (iidSequenceLaw ν)
        (blockPrefixExceedance (start n) (length n) (threshold n) ∩
          blockPrefixExceedance (start n + length n) (length n) (threshold n)) ≤
        bound n ^ 2 := by
  filter_upwards [hbound] with n hboundN
  exact measure_inter_adjacentBlockPrefixExceedance_le_sq_of_bound ν
    (start n) (length n) (threshold n) (bound n) hboundN

end ProbabilityTheory.RandomWalk

end

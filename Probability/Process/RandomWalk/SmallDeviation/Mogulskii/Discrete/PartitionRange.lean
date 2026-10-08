/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.Horizontal
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal

/-!
# Finite-partition range upper bound

On each partition cell, confinement to a fixed open interval forces the
increment block's partial-sum range below the interval width. Distinct cells
use disjoint IID coordinate blocks, so the probability is bounded by the
product of their one-cell range probabilities.
-/

open MeasureTheory
open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

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

/-- Oscillation of a block before its final coordinate. This is the event that
arises on a half-open time cell: the value at the right knot belongs to the
next cell, so the preceding cell only constrains positions at offsets strictly
less than its full block length. -/
def blockOscillationPrefixLTEvent (width : ℝ) (length : ℕ) :
    Set (Fin length → ℝ) :=
  {increments | ∀ i j : Fin length,
    |Fin.partialSum increments i.castSucc -
      Fin.partialSum increments j.castSucc| < width}

private theorem measurable_partialSumPrefix {length : ℕ}
    (time : Fin (length + 1)) :
    Measurable (fun increments : Fin length → ℝ =>
      Fin.partialSum increments time) := by
  induction time using Fin.induction with
  | zero => exact measurable_const
  | succ time ih =>
    have hm := ih.add (measurable_pi_apply time)
    have heq : (fun increments : Fin length → ℝ =>
        Fin.partialSum increments time.succ) =
      (fun increments : Fin length → ℝ =>
        Fin.partialSum increments time.castSucc) +
        (fun increments : Fin length → ℝ => increments time) := by
      funext increments
      simp only [Fin.partialSum_succ, Pi.add_apply]
    exact heq ▸ hm

/-- The open range event that observes every partial sum before the final
coordinate of a finite increment block is measurable. -/
theorem measurableSet_blockOscillationPrefixLTEvent (width : ℝ) (length : ℕ) :
    MeasurableSet (blockOscillationPrefixLTEvent width length) := by
  rw [show blockOscillationPrefixLTEvent width length =
      ⋂ i : Fin length, ⋂ j : Fin length,
        {increments : Fin length → ℝ |
          |Fin.partialSum increments i.castSucc -
            Fin.partialSum increments j.castSucc| < width} by
    ext increments
    simp [blockOscillationPrefixLTEvent]]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => by
    have hdiff : Measurable (fun increments : Fin length → ℝ =>
        Fin.partialSum increments i.castSucc -
          Fin.partialSum increments j.castSucc) :=
      (measurable_partialSumPrefix i.castSucc).sub
        (measurable_partialSumPrefix j.castSucc)
    exact measurableSet_Iio.preimage
      (continuous_abs.measurable.comp hdiff)

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

/-- On each half-open partition cell, confinement to an open interval gives a
strict range bound for the partial sums before the cell's terminal increment.
The IID probabilities of these cell events factor, including when cell lengths
vary. -/
theorem measure_forall_halfOpenPartitionCellCorridors_le_prod_rangeProbability
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (blocks : ℕ) (length : ℕ → ℕ)
    (lower upper : Fin blocks → ℝ)
    (hlength : ∀ j : Fin blocks, 0 < length j.val) :
    iidSequenceLaw ν {increment : ℕ → ℝ |
      ∀ j : Fin blocks, ∀ k < length j.val,
        lower j < AdditivePath.displacement
            (AdditivePath.blockStart length j.val + k) increment ∧
        AdditivePath.displacement
            (AdditivePath.blockStart length j.val + k) increment < upper j} ≤
      ∏ j : Fin blocks,
        partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
          (upper j - lower j) (length j.val - 1) := by
  let blockEvent : (j : Fin blocks) → Set (Fin (length j.val) → ℝ) := fun j =>
    blockOscillationPrefixLTEvent (upper j - lower j) (length j.val)
  have hfactor := ProbabilityTheory.RandomWalk.iidSequenceLaw_measure_forall_variableConsecutiveBlockEvent
    ν length blocks blockEvent (fun j =>
      measurableSet_blockOscillationPrefixLTEvent
        (upper j - lower j) (length j.val))
  have hfactor' : iidSequenceLaw ν {increment : ℕ → ℝ |
      ∀ j : Fin blocks,
        Combinatorics.Sequence.blockCoordinates
          (AdditivePath.blockStart length j.val) (length j.val) increment ∈
            blockEvent j} =
      ∏ j : Fin blocks, iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 (length j.val) increment ∈
          blockEvent j} := by
    simpa [blockEvent] using hfactor
  have hsubset :
      {increment : ℕ → ℝ |
        ∀ j : Fin blocks, ∀ k < length j.val,
          lower j < AdditivePath.displacement
              (AdditivePath.blockStart length j.val + k) increment ∧
          AdditivePath.displacement
              (AdditivePath.blockStart length j.val + k) increment < upper j} ⊆
      {increment : ℕ → ℝ |
        ∀ j : Fin blocks,
          Combinatorics.Sequence.blockCoordinates
            (AdditivePath.blockStart length j.val) (length j.val) increment ∈
              blockEvent j} := by
    intro increment hconfined j
    change ∀ i k : Fin (length j.val),
      |Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates
            (AdditivePath.blockStart length j.val) (length j.val) increment)
          i.castSucc -
        Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates
            (AdditivePath.blockStart length j.val) (length j.val) increment)
          k.castSucc| < upper j - lower j
    intro i k
    have hi := hconfined j i.val i.isLt
    have hk := hconfined j k.val k.isLt
    have hvalue (offset : Fin (length j.val)) :
        Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates
              (AdditivePath.blockStart length j.val) (length j.val) increment)
            offset.castSucc =
          AdditivePath.displacement
              (AdditivePath.blockStart length j.val + (offset : ℕ)) increment -
            AdditivePath.displacement (AdditivePath.blockStart length j.val) increment := by
      rw [partialSum_blockCoordinates]
      simp only [Fin.val_castSucc]
      have h := AdditivePath.displacement_add_eq_add_blockSum
        (AdditivePath.blockStart length j.val) (offset : ℕ) increment
      linarith
    have hupper :
        AdditivePath.displacement
            (AdditivePath.blockStart length j.val + (i : ℕ)) increment -
          AdditivePath.displacement
            (AdditivePath.blockStart length j.val + (k : ℕ)) increment <
          upper j - lower j := by
      linarith [hi.2, hk.1]
    have hlower' :
        -(upper j - lower j) <
          AdditivePath.displacement
              (AdditivePath.blockStart length j.val + (i : ℕ)) increment -
            AdditivePath.displacement
              (AdditivePath.blockStart length j.val + (k : ℕ)) increment := by
      linarith [hi.1, hk.2]
    have hcancel :
        (AdditivePath.displacement
              (AdditivePath.blockStart length j.val + (i : ℕ)) increment -
            AdditivePath.displacement (AdditivePath.blockStart length j.val) increment) -
          (AdditivePath.displacement
              (AdditivePath.blockStart length j.val + (k : ℕ)) increment -
            AdditivePath.displacement (AdditivePath.blockStart length j.val) increment) =
          AdditivePath.displacement
              (AdditivePath.blockStart length j.val + (i : ℕ)) increment -
            AdditivePath.displacement
              (AdditivePath.blockStart length j.val + (k : ℕ)) increment := by
      ring
    rw [hvalue i, hvalue k, hcancel]
    exact abs_lt.mpr ⟨hlower', hupper⟩
  calc
    _ ≤ iidSequenceLaw ν {increment : ℕ → ℝ |
          ∀ j : Fin blocks,
            Combinatorics.Sequence.blockCoordinates
              (AdditivePath.blockStart length j.val) (length j.val) increment ∈
                blockEvent j} := measure_mono hsubset
    _ = ∏ j : Fin blocks, iidSequenceLaw ν {increment : ℕ → ℝ |
          Combinatorics.Sequence.blockCoordinates 0 (length j.val) increment ∈
            blockEvent j} := hfactor'
    _ = ∏ j : Fin blocks,
          partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
            (upper j - lower j) (length j.val - 1) := by
      apply Finset.prod_congr rfl
      intro j hj
      change iidSequenceLaw ν {increment : ℕ → ℝ |
          blockOscillationPrefixLTEvent (upper j - lower j) (length j.val)
            (Combinatorics.Sequence.blockCoordinates 0 (length j.val) increment)} = _
      exact iidSequenceLaw_blockOscillationPrefixLTEvent_eq_partialSumRangeProbability
        ν (hlength j)

/-- A finite family of open interval constraints on consecutive walk segments
is bounded by the product of the translation-invariant range probabilities
of those segments. The segment lengths may vary. -/
theorem measure_forall_partitionCellCorridors_le_prod_rangeProbability
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (blocks : ℕ) (length : ℕ → ℕ)
    (lower upper : Fin blocks → ℝ) :
    iidSequenceLaw ν {increment : ℕ → ℝ |
      ∀ j : Fin blocks, ∀ k ≤ length j.val,
        lower j < AdditivePath.displacement
            (AdditivePath.blockStart length j.val + k) increment ∧
        AdditivePath.displacement
            (AdditivePath.blockStart length j.val + k) increment < upper j} ≤
      ∏ j : Fin blocks,
        partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
          (upper j - lower j) (length j.val) := by
  let blockEvent : (j : Fin blocks) → Set (Fin (length j.val) → ℝ) := fun j =>
    blockOscillationLTEvent (upper j - lower j) (length j.val)
  have hfactor := ProbabilityTheory.RandomWalk.iidSequenceLaw_measure_forall_variableConsecutiveBlockEvent
    ν length blocks blockEvent (fun j =>
      measurableSet_blockOscillationLTEvent (upper j - lower j) (length j.val))
  have hfactor' : iidSequenceLaw ν {increment : ℕ → ℝ |
      ∀ j : Fin blocks,
        Combinatorics.Sequence.blockCoordinates
          (AdditivePath.blockStart length j.val) (length j.val) increment ∈
            blockEvent j} =
      ∏ j : Fin blocks, iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 (length j.val) increment ∈
          blockEvent j} := by
    simpa [blockEvent] using hfactor
  have hsubset :
      {increment : ℕ → ℝ |
        ∀ j : Fin blocks, ∀ k ≤ length j.val,
          lower j < AdditivePath.displacement
              (AdditivePath.blockStart length j.val + k) increment ∧
          AdditivePath.displacement
              (AdditivePath.blockStart length j.val + k) increment < upper j} ⊆
      {increment : ℕ → ℝ |
        ∀ j : Fin blocks,
          Combinatorics.Sequence.blockCoordinates
            (AdditivePath.blockStart length j.val) (length j.val) increment ∈
              blockEvent j} := by
    intro increment hconfined j
    change ∀ i k : Fin (length j.val + 1),
      |Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates
            (AdditivePath.blockStart length j.val) (length j.val) increment) i -
        Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates
            (AdditivePath.blockStart length j.val) (length j.val) increment) k| <
        upper j - lower j
    intro i k
    have hi := hconfined j i.val (Nat.le_of_lt_succ i.isLt)
    have hk := hconfined j k.val (Nat.le_of_lt_succ k.isLt)
    have hvalue (offset : Fin (length j.val + 1)) :
        Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates
              (AdditivePath.blockStart length j.val) (length j.val) increment)
            offset =
          AdditivePath.displacement
              (AdditivePath.blockStart length j.val + (offset : ℕ)) increment -
            AdditivePath.displacement (AdditivePath.blockStart length j.val) increment := by
      rw [partialSum_blockCoordinates]
      have h := AdditivePath.displacement_add_eq_add_blockSum
        (AdditivePath.blockStart length j.val) (offset : ℕ) increment
      linarith
    have hupper :
        AdditivePath.displacement
            (AdditivePath.blockStart length j.val + (i : ℕ)) increment -
          AdditivePath.displacement
            (AdditivePath.blockStart length j.val + (k : ℕ)) increment <
          upper j - lower j := by
      linarith [hi.2, hk.1]
    have hlower :
        -(upper j - lower j) <
          AdditivePath.displacement
              (AdditivePath.blockStart length j.val + (i : ℕ)) increment -
            AdditivePath.displacement
              (AdditivePath.blockStart length j.val + (k : ℕ)) increment := by
      linarith [hi.1, hk.2]
    have hcancel :
        (AdditivePath.displacement
              (AdditivePath.blockStart length j.val + (i : ℕ)) increment -
            AdditivePath.displacement (AdditivePath.blockStart length j.val) increment) -
          (AdditivePath.displacement
              (AdditivePath.blockStart length j.val + (k : ℕ)) increment -
            AdditivePath.displacement (AdditivePath.blockStart length j.val) increment) =
          AdditivePath.displacement
              (AdditivePath.blockStart length j.val + (i : ℕ)) increment -
            AdditivePath.displacement
              (AdditivePath.blockStart length j.val + (k : ℕ)) increment := by
      ring
    rw [hvalue i, hvalue k, hcancel]
    exact abs_lt.mpr ⟨hlower, hupper⟩
  calc
    _ ≤ iidSequenceLaw ν {increment : ℕ → ℝ |
          ∀ j : Fin blocks,
            Combinatorics.Sequence.blockCoordinates
              (AdditivePath.blockStart length j.val) (length j.val) increment ∈
                blockEvent j} := measure_mono hsubset
    _ = ∏ j : Fin blocks, iidSequenceLaw ν {increment : ℕ → ℝ |
          Combinatorics.Sequence.blockCoordinates 0 (length j.val) increment ∈
            blockEvent j} := hfactor'
    _ = ∏ j : Fin blocks,
          partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
            (upper j - lower j) (length j.val) := by
      apply Finset.prod_congr rfl
      intro j hj
      change iidSequenceLaw ν {increment : ℕ → ℝ |
          blockOscillationLTEvent (upper j - lower j) (length j.val)
            (Combinatorics.Sequence.blockCoordinates 0 (length j.val) increment)} = _
      exact iidSequenceLaw_blockOscillationLTEvent_eq_partialSumRangeProbability
        ν (upper j - lower j) (length j.val)

/-! ## Selected cells -/

/-- The half-open partition estimate on a selected finite set of cells.
Unselected cells impose no condition and contribute the factor one. This is
needed for extended-real corridors, where cells with an infinite boundary
have no finite-width range cost. -/
theorem measure_forall_selectedHalfOpenPartitionCellCorridors_le_prod_rangeProbability
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (blocks : ℕ) (length : ℕ → ℕ)
    (s : Finset (Fin blocks))
    (lower upper : Fin blocks → ℝ)
    (hlength : ∀ j ∈ s, 0 < length j.val) :
    iidSequenceLaw ν {increment : ℕ → ℝ |
      ∀ j ∈ s, ∀ k < length j.val,
        lower j < AdditivePath.displacement
            (AdditivePath.blockStart length j.val + k) increment ∧
        AdditivePath.displacement
            (AdditivePath.blockStart length j.val + k) increment < upper j} ≤
      ∏ j ∈ s,
        partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
          (upper j - lower j) (length j.val - 1) := by
  let blockEvent : (j : Fin blocks) → Set (Fin (length j.val) → ℝ) := fun j =>
    if j ∈ s then
      blockOscillationPrefixLTEvent (upper j - lower j) (length j.val)
    else Set.univ
  let oneBlockEvent (j : Fin blocks) : Set (ℕ → ℝ) :=
    {increment | Combinatorics.Sequence.blockCoordinates 0 (length j.val)
      increment ∈ blockEvent j}
  have hfactor :=
    ProbabilityTheory.RandomWalk.iidSequenceLaw_measure_forall_variableConsecutiveBlockEvent
      ν length blocks blockEvent (by
        intro j
        by_cases hj : j ∈ s
        · simp only [blockEvent, ite_eq_left hj]
          exact measurableSet_blockOscillationPrefixLTEvent
            (upper j - lower j) (length j.val)
        · simp [blockEvent, hj])
  have hsubset :
      {increment : ℕ → ℝ |
        ∀ j ∈ s, ∀ k < length j.val,
          lower j < AdditivePath.displacement
              (AdditivePath.blockStart length j.val + k) increment ∧
          AdditivePath.displacement
              (AdditivePath.blockStart length j.val + k) increment < upper j} ⊆
      {increment : ℕ → ℝ |
        ∀ j : Fin blocks,
          Combinatorics.Sequence.blockCoordinates
            (AdditivePath.blockStart length j.val) (length j.val) increment ∈
              blockEvent j} := by
    intro increment h j
    by_cases hj : j ∈ s
    · simp only [blockEvent, ite_eq_left hj]
      change ∀ i k : Fin (length j.val),
        |Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates
              (AdditivePath.blockStart length j.val) (length j.val) increment)
            i.castSucc -
          Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates
              (AdditivePath.blockStart length j.val) (length j.val) increment)
            k.castSucc| < upper j - lower j
      intro i k
      have hi := h j hj i.val i.isLt
      have hk := h j hj k.val k.isLt
      have hvalue (offset : Fin (length j.val)) :
          Fin.partialSum
              (Combinatorics.Sequence.blockCoordinates
                (AdditivePath.blockStart length j.val) (length j.val) increment)
              offset.castSucc =
            AdditivePath.displacement
                (AdditivePath.blockStart length j.val + (offset : ℕ)) increment -
              AdditivePath.displacement (AdditivePath.blockStart length j.val)
                increment := by
        rw [partialSum_blockCoordinates]
        simp only [Fin.val_castSucc]
        have h := AdditivePath.displacement_add_eq_add_blockSum
          (AdditivePath.blockStart length j.val) (offset : ℕ) increment
        linarith
      have hupper :
          AdditivePath.displacement
              (AdditivePath.blockStart length j.val + (i : ℕ)) increment -
            AdditivePath.displacement
              (AdditivePath.blockStart length j.val + (k : ℕ)) increment <
            upper j - lower j := by
        linarith [hi.2, hk.1]
      have hlower' :
          -(upper j - lower j) <
            AdditivePath.displacement
                (AdditivePath.blockStart length j.val + (i : ℕ)) increment -
              AdditivePath.displacement
                (AdditivePath.blockStart length j.val + (k : ℕ)) increment := by
        linarith [hi.1, hk.2]
      have hcancel :
          (AdditivePath.displacement
                (AdditivePath.blockStart length j.val + (i : ℕ)) increment -
              AdditivePath.displacement (AdditivePath.blockStart length j.val)
                increment) -
            (AdditivePath.displacement
                (AdditivePath.blockStart length j.val + (k : ℕ)) increment -
              AdditivePath.displacement (AdditivePath.blockStart length j.val)
                increment) =
          AdditivePath.displacement
              (AdditivePath.blockStart length j.val + (i : ℕ)) increment -
            AdditivePath.displacement
              (AdditivePath.blockStart length j.val + (k : ℕ)) increment := by
        ring
      rw [hvalue i, hvalue k, hcancel]
      exact abs_lt.mpr ⟨hlower', hupper⟩
    · simp [blockEvent, hj]
  have hone (j : Fin blocks) (hj : j ∈ s) :
      iidSequenceLaw ν (oneBlockEvent j) =
        partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
          (upper j - lower j) (length j.val - 1) := by
    have hevent : oneBlockEvent j = {increment : ℕ → ℝ |
        blockOscillationPrefixLTEvent (upper j - lower j) (length j.val)
          (Combinatorics.Sequence.blockCoordinates 0 (length j.val) increment)} := by
      ext increment
      simp only [oneBlockEvent, blockEvent]
      rw [ite_eq_left hj]
      rfl
    rw [hevent]
    exact iidSequenceLaw_blockOscillationPrefixLTEvent_eq_partialSumRangeProbability
      ν (hlength j hj)
  have houtside (j : Fin blocks) (hj : j ∉ s) :
      iidSequenceLaw ν (oneBlockEvent j) = 1 := by
    simp [oneBlockEvent, blockEvent, hj]
  calc
    iidSequenceLaw ν {increment : ℕ → ℝ |
        ∀ j ∈ s, ∀ k < length j.val,
          lower j < AdditivePath.displacement
              (AdditivePath.blockStart length j.val + k) increment ∧
          AdditivePath.displacement
              (AdditivePath.blockStart length j.val + k) increment < upper j} ≤
      iidSequenceLaw ν {increment : ℕ → ℝ |
        ∀ j : Fin blocks,
          Combinatorics.Sequence.blockCoordinates
            (AdditivePath.blockStart length j.val) (length j.val) increment ∈
              blockEvent j} := measure_mono hsubset
    _ = ∏ j : Fin blocks, iidSequenceLaw ν (oneBlockEvent j) := by
      simpa [oneBlockEvent] using hfactor
    _ = ∏ j ∈ s,
          partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
            (upper j - lower j) (length j.val - 1) := by
      symm
      calc
        ∏ j ∈ s,
            partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
              (upper j - lower j) (length j.val - 1) =
          ∏ j ∈ s, iidSequenceLaw ν (oneBlockEvent j) := by
            apply Finset.prod_congr rfl
            intro j hj
            exact (hone j hj).symm
        _ = ∏ j : Fin blocks, iidSequenceLaw ν (oneBlockEvent j) := by
          apply Finset.prod_subset (Finset.subset_univ s)
          intro j hj hjnot
          exact houtside j hjnot

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Oscillation
public import Probability.Process.RandomWalk.Path.Block.Law.Oscillation
public import Probability.Process.RandomWalk.Path.Block.Law.Basic
public import Probability.Process.RandomWalk.Path.Block.Partition.Basic

/-!
# Range bounds for partitioned random walks

For an IID increment sequence, confinement of each disjoint partial-sum block
in a prescribed interval bounds the probability by a product of the
corresponding one-block range probabilities. The half-open version leaves the
terminal increment of each block unrestricted.

The public declarations are:

- `measure_forall_halfOpenPartitionCellCorridors_le_prod_rangeProbability`:
  the product bound for half-open cells, with each cell's terminal increment
  assigned to the next cell.
- `measure_forall_partitionCellCorridors_le_prod_rangeProbability`:
  the product bound when each block includes its terminal position.
- `measure_forall_selectedHalfOpenPartitionCellCorridors_le_prod_rangeProbability`:
  the half-open bound for any selected finite family of cells.
-/

open MeasureTheory
open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory.RandomWalk

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

end ProbabilityTheory.RandomWalk

end

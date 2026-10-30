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
public import Probability.Process.RandomWalk.Path.Event.Oscillation
import Probability.Sequence.IID.Blocks.Consecutive

/-!
# Range bounds for partitioned random walks

For an IID increment sequence, confinement of each disjoint partial-sum block
in a prescribed interval bounds the probability by a product of the
corresponding one-block range probabilities. The half-open version leaves the
terminal increment of each block unrestricted. A strict range bound on the
whole finite walk also bounds the probability by the product probability for
any number of covered equal-length oscillation blocks.

## Public declarations

* `measure_forall_halfOpenPartitionCellCorridors_le_prod_rangeProbability`
  bounds the probability of strict confinement before each block endpoint by
  the product of the one-block range probabilities at lengths `length j - 1`.
* `measure_forall_partitionCellCorridors_le_prod_rangeProbability` bounds
  strict confinement through each block endpoint by the product of the
  one-block range probabilities at lengths `length j`.
* `measure_forall_selectedHalfOpenPartitionCellCorridors_le_prod_rangeProbability`
  gives the corresponding product bound for an arbitrary finite selected
  family of half-open cells.
* `iidSequenceLaw_measure_partialSumRangeLT_le_pow_blockOscillationLT_of_blockCover`
  states that if $qm\le N$, then
  $\mathbb P(\operatorname{range}(S_0,\ldots,S_N)<w)\le
  \mathbb P(\operatorname{osc}(S_0,\ldots,S_m)<w)^q$.
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
            (Combinatorics.Sequence.blockStart length j.val + k) increment ∧
        AdditivePath.displacement
            (Combinatorics.Sequence.blockStart length j.val + k) increment < upper j} ≤
      ∏ j : Fin blocks,
        partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
          (upper j - lower j) (length j.val - 1) := by
  let blockEvent : (j : Fin blocks) → Set (Fin (length j.val) → ℝ) := fun j =>
    blockOscillationPrefixLTEvent (upper j - lower j) (length j.val)
  have hfactor := ProbabilityTheory.iidSequenceLaw_measure_forall_variableConsecutiveBlockEvent
    ν length blocks blockEvent (fun j =>
      measurableSet_blockOscillationPrefixLTEvent
        (upper j - lower j) (length j.val))
  have hfactor' : iidSequenceLaw ν {increment : ℕ → ℝ |
      ∀ j : Fin blocks,
        Combinatorics.Sequence.blockCoordinates
          (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment ∈
            blockEvent j} =
      ∏ j : Fin blocks, iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 (length j.val) increment ∈
          blockEvent j} := by
    simpa [blockEvent] using hfactor
  have hsubset :
      {increment : ℕ → ℝ |
        ∀ j : Fin blocks, ∀ k < length j.val,
          lower j < AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + k) increment ∧
          AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + k) increment < upper j} ⊆
      {increment : ℕ → ℝ |
        ∀ j : Fin blocks,
          Combinatorics.Sequence.blockCoordinates
            (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment ∈
              blockEvent j} := by
    intro increment hconfined j
    change ∀ i k : Fin (length j.val),
      |Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates
            (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment)
          i.castSucc -
        Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates
            (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment)
          k.castSucc| < upper j - lower j
    intro i k
    have hi := hconfined j i.val i.isLt
    have hk := hconfined j k.val k.isLt
    have hvalue (offset : Fin (length j.val)) :
        Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates
              (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment)
            offset.castSucc =
          AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + (offset : ℕ)) increment -
            AdditivePath.displacement (Combinatorics.Sequence.blockStart length j.val) increment := by
      rw [partialSum_blockCoordinates]
      simp only [Fin.val_castSucc]
      have h := AdditivePath.displacement_add_eq_add_blockSum
        (Combinatorics.Sequence.blockStart length j.val) (offset : ℕ) increment
      linarith
    have hupper :
        AdditivePath.displacement
            (Combinatorics.Sequence.blockStart length j.val + (i : ℕ)) increment -
          AdditivePath.displacement
            (Combinatorics.Sequence.blockStart length j.val + (k : ℕ)) increment <
          upper j - lower j := by
      linarith [hi.2, hk.1]
    have hlower' :
        -(upper j - lower j) <
          AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + (i : ℕ)) increment -
            AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + (k : ℕ)) increment := by
      linarith [hi.1, hk.2]
    have hcancel :
        (AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + (i : ℕ)) increment -
            AdditivePath.displacement (Combinatorics.Sequence.blockStart length j.val) increment) -
          (AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + (k : ℕ)) increment -
            AdditivePath.displacement (Combinatorics.Sequence.blockStart length j.val) increment) =
          AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + (i : ℕ)) increment -
            AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + (k : ℕ)) increment := by
      ring
    rw [hvalue i, hvalue k, hcancel]
    exact abs_lt.mpr ⟨hlower', hupper⟩
  calc
    _ ≤ iidSequenceLaw ν {increment : ℕ → ℝ |
          ∀ j : Fin blocks,
            Combinatorics.Sequence.blockCoordinates
              (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment ∈
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
            (Combinatorics.Sequence.blockStart length j.val + k) increment ∧
        AdditivePath.displacement
            (Combinatorics.Sequence.blockStart length j.val + k) increment < upper j} ≤
      ∏ j : Fin blocks,
        partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
          (upper j - lower j) (length j.val) := by
  let blockEvent : (j : Fin blocks) → Set (Fin (length j.val) → ℝ) := fun j =>
    blockOscillationLTEvent (upper j - lower j) (length j.val)
  have hfactor := ProbabilityTheory.iidSequenceLaw_measure_forall_variableConsecutiveBlockEvent
    ν length blocks blockEvent (fun j =>
      measurableSet_blockOscillationLTEvent (upper j - lower j) (length j.val))
  have hfactor' : iidSequenceLaw ν {increment : ℕ → ℝ |
      ∀ j : Fin blocks,
        Combinatorics.Sequence.blockCoordinates
          (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment ∈
            blockEvent j} =
      ∏ j : Fin blocks, iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 (length j.val) increment ∈
          blockEvent j} := by
    simpa [blockEvent] using hfactor
  have hsubset :
      {increment : ℕ → ℝ |
        ∀ j : Fin blocks, ∀ k ≤ length j.val,
          lower j < AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + k) increment ∧
          AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + k) increment < upper j} ⊆
      {increment : ℕ → ℝ |
        ∀ j : Fin blocks,
          Combinatorics.Sequence.blockCoordinates
            (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment ∈
              blockEvent j} := by
    intro increment hconfined j
    change ∀ i k : Fin (length j.val + 1),
      |Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates
            (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment) i -
        Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates
            (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment) k| <
        upper j - lower j
    intro i k
    have hi := hconfined j i.val (Nat.le_of_lt_succ i.isLt)
    have hk := hconfined j k.val (Nat.le_of_lt_succ k.isLt)
    have hvalue (offset : Fin (length j.val + 1)) :
        Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates
              (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment)
            offset =
          AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + (offset : ℕ)) increment -
            AdditivePath.displacement (Combinatorics.Sequence.blockStart length j.val) increment := by
      rw [partialSum_blockCoordinates]
      have h := AdditivePath.displacement_add_eq_add_blockSum
        (Combinatorics.Sequence.blockStart length j.val) (offset : ℕ) increment
      linarith
    have hupper :
        AdditivePath.displacement
            (Combinatorics.Sequence.blockStart length j.val + (i : ℕ)) increment -
          AdditivePath.displacement
            (Combinatorics.Sequence.blockStart length j.val + (k : ℕ)) increment <
          upper j - lower j := by
      linarith [hi.2, hk.1]
    have hlower :
        -(upper j - lower j) <
          AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + (i : ℕ)) increment -
            AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + (k : ℕ)) increment := by
      linarith [hi.1, hk.2]
    have hcancel :
        (AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + (i : ℕ)) increment -
            AdditivePath.displacement (Combinatorics.Sequence.blockStart length j.val) increment) -
          (AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + (k : ℕ)) increment -
            AdditivePath.displacement (Combinatorics.Sequence.blockStart length j.val) increment) =
          AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + (i : ℕ)) increment -
            AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + (k : ℕ)) increment := by
      ring
    rw [hvalue i, hvalue k, hcancel]
    exact abs_lt.mpr ⟨hlower, hupper⟩
  calc
    _ ≤ iidSequenceLaw ν {increment : ℕ → ℝ |
          ∀ j : Fin blocks,
            Combinatorics.Sequence.blockCoordinates
              (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment ∈
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
            (Combinatorics.Sequence.blockStart length j.val + k) increment ∧
        AdditivePath.displacement
            (Combinatorics.Sequence.blockStart length j.val + k) increment < upper j} ≤
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
    ProbabilityTheory.iidSequenceLaw_measure_forall_variableConsecutiveBlockEvent
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
              (Combinatorics.Sequence.blockStart length j.val + k) increment ∧
          AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + k) increment < upper j} ⊆
      {increment : ℕ → ℝ |
        ∀ j : Fin blocks,
          Combinatorics.Sequence.blockCoordinates
            (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment ∈
              blockEvent j} := by
    intro increment h j
    by_cases hj : j ∈ s
    · simp only [blockEvent, ite_eq_left hj]
      change ∀ i k : Fin (length j.val),
        |Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates
              (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment)
            i.castSucc -
          Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates
              (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment)
            k.castSucc| < upper j - lower j
      intro i k
      have hi := h j hj i.val i.isLt
      have hk := h j hj k.val k.isLt
      have hvalue (offset : Fin (length j.val)) :
          Fin.partialSum
              (Combinatorics.Sequence.blockCoordinates
                (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment)
              offset.castSucc =
            AdditivePath.displacement
                (Combinatorics.Sequence.blockStart length j.val + (offset : ℕ)) increment -
              AdditivePath.displacement (Combinatorics.Sequence.blockStart length j.val)
                increment := by
        rw [partialSum_blockCoordinates]
        simp only [Fin.val_castSucc]
        have h := AdditivePath.displacement_add_eq_add_blockSum
          (Combinatorics.Sequence.blockStart length j.val) (offset : ℕ) increment
        linarith
      have hupper :
          AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + (i : ℕ)) increment -
            AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + (k : ℕ)) increment <
            upper j - lower j := by
        linarith [hi.2, hk.1]
      have hlower' :
          -(upper j - lower j) <
            AdditivePath.displacement
                (Combinatorics.Sequence.blockStart length j.val + (i : ℕ)) increment -
              AdditivePath.displacement
                (Combinatorics.Sequence.blockStart length j.val + (k : ℕ)) increment := by
        linarith [hi.1, hk.2]
      have hcancel :
          (AdditivePath.displacement
                (Combinatorics.Sequence.blockStart length j.val + (i : ℕ)) increment -
              AdditivePath.displacement (Combinatorics.Sequence.blockStart length j.val)
                increment) -
            (AdditivePath.displacement
                (Combinatorics.Sequence.blockStart length j.val + (k : ℕ)) increment -
              AdditivePath.displacement (Combinatorics.Sequence.blockStart length j.val)
                increment) =
          AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + (i : ℕ)) increment -
            AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + (k : ℕ)) increment := by
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
              (Combinatorics.Sequence.blockStart length j.val + k) increment ∧
          AdditivePath.displacement
              (Combinatorics.Sequence.blockStart length j.val + k) increment < upper j} ≤
      iidSequenceLaw ν {increment : ℕ → ℝ |
        ∀ j : Fin blocks,
          Combinatorics.Sequence.blockCoordinates
            (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment ∈
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

/-- A strict range bound on a whole finite walk forces the same strict range
bound on every complete equal-length increment block. The block events are
independent, so the whole-path probability is bounded by the one-block
probability raised to the number of covered blocks.

This finite-time estimate is Mogul'skii, Lemma 3(c), equation (32), in
“Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755--765; English translation, “Small Deviations
in a Space of Trajectories,” *Theory of Probability and Its Applications*
19(4) (1975), 726--736, DOI 10.1137/1119081. -/
theorem iidSequenceLaw_measure_partialSumRangeLT_le_pow_blockOscillationLT_of_blockCover
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (width : ℝ) (blocks length horizon : ℕ)
    (hcover : blocks * length ≤ horizon) :
    partialSumRangeOscillationLTProbability (iidSequenceLaw ν) width horizon ≤
      (iidSequenceLaw ν {increment |
        blockOscillationLTEvent width length
          (Combinatorics.Sequence.blockCoordinates 0 length increment)}) ^ blocks := by
  change iidSequenceLaw ν {increment : ℕ → ℝ | ∀ i j : Fin (horizon + 1),
    |AdditivePath.displacement (i : ℕ) increment -
      AdditivePath.displacement (j : ℕ) increment| < width} ≤ _
  have hsubset :
      {increment : ℕ → ℝ | ∀ i j : Fin (horizon + 1),
        |AdditivePath.displacement (i : ℕ) increment -
          AdditivePath.displacement (j : ℕ) increment| < width} ⊆
      {increment : ℕ → ℝ | ∀ j : Fin blocks,
        blockOscillationLTEvent width length
          (Combinatorics.Sequence.blockCoordinates (j * length) length increment)} := by
    intro increment hrange j
    change ∀ i k : Fin (length + 1),
      |Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates (j * length) length increment) i -
        Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates (j * length) length increment) k| < width
    intro i k
    have htime (offset : Fin (length + 1)) :
        j * length + (offset : ℕ) ≤ horizon := by
      have hoffset : (offset : ℕ) ≤ length := Nat.le_of_lt_succ offset.isLt
      calc
        j * length + (offset : ℕ) ≤ j * length + length :=
          Nat.add_le_add_left hoffset _
        _ = (j + 1) * length := by simp [Nat.succ_mul]
        _ ≤ blocks * length :=
          Nat.mul_le_mul_right length (Nat.succ_le_iff.mpr j.isLt)
        _ ≤ horizon := hcover
    have hvalue (offset : Fin (length + 1)) :
        Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates (j * length) length increment)
            offset =
          AdditivePath.displacement (j * length + (offset : ℕ)) increment -
            AdditivePath.displacement (j * length) increment := by
      rw [partialSum_blockCoordinates]
      have h := AdditivePath.displacement_add_eq_add_blockSum
        (j * length) (offset : ℕ) increment
      linarith
    let ti : Fin (horizon + 1) :=
      ⟨j * length + (i : ℕ), Nat.lt_succ_of_le (htime i)⟩
    let tk : Fin (horizon + 1) :=
      ⟨j * length + (k : ℕ), Nat.lt_succ_of_le (htime k)⟩
    rw [hvalue i, hvalue k]
    have hcancel :
        (AdditivePath.displacement (j * length + (i : ℕ)) increment -
            AdditivePath.displacement (j * length) increment) -
          (AdditivePath.displacement (j * length + (k : ℕ)) increment -
            AdditivePath.displacement (j * length) increment) =
          AdditivePath.displacement (ti : ℕ) increment -
            AdditivePath.displacement (tk : ℕ) increment := by
      simp only [ti, tk]
      ring
    rw [hcancel]
    exact hrange ti tk
  calc
    _ ≤ iidSequenceLaw ν {increment : ℕ → ℝ | ∀ j : Fin blocks,
          blockOscillationLTEvent width length
            (Combinatorics.Sequence.blockCoordinates (j * length) length increment)} :=
      measure_mono hsubset
    _ = (iidSequenceLaw ν {increment |
          blockOscillationLTEvent width length
            (Combinatorics.Sequence.blockCoordinates 0 length increment)}) ^ blocks :=
      iidSequenceLaw_measure_forall_consecutiveBlockEvent ν blocks length
        (blockOscillationLTEvent width length)
        (measurableSet_blockOscillationLTEvent width length)

end ProbabilityTheory.RandomWalk

end

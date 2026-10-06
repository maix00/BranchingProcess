/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Partition.Basic
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Basic
public import Probability.Process.RandomWalk.Path.Oscillation
public import Probability.Process.RandomWalk.Path.Block.Law
public import Probability.Process.RandomWalk.Kernel.Killed.Return
public import Probability.Process.RandomWalk.Kernel.Killed.Blocking
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal

/-!
# Discrete horizontal block inequalities

These are finite-time inequalities for a walk with IID increments.  The
horizontal upper bound is the discrete block comparison used in Mogulskii's
Lemma 3: a path confined to one interval has bounded oscillation on every
sub-block, and disjoint increment blocks are independent.
-/

open MeasureTheory
open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii


/-- The event that the partial-sum path of one finite increment block has
oscillation at most `width`. -/
def blockOscillationEvent (width : ℝ) (length : ℕ) :
    Set (Fin length → ℝ) :=
  {increments | OscillationBounded
    (fun time : Fin (length + 1) => Fin.partialSum increments time) width}

private theorem measurable_partialSum {length : ℕ}
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

/-- The finite-block oscillation event is measurable. -/
theorem measurableSet_blockOscillationEvent (width : ℝ) (length : ℕ) :
    MeasurableSet (blockOscillationEvent width length) := by
  rw [show blockOscillationEvent width length =
      ⋂ i : Fin (length + 1), ⋂ j : Fin (length + 1),
        {increments : Fin length → ℝ |
          |Fin.partialSum increments i - Fin.partialSum increments j| ≤
            width} by
    ext increments
    simp [blockOscillationEvent, OscillationBounded]]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => by
    have hdiff : Measurable (fun increments : Fin length → ℝ =>
        Fin.partialSum increments i - Fin.partialSum increments j) :=
      (measurable_partialSum i).sub (measurable_partialSum j)
    exact measurableSet_Iic.preimage
      (continuous_abs.measurable.comp hdiff)

/-- The probability that every one of a finite family of consecutive IID
increment blocks has oscillation at most `width` is the corresponding power
of the one-block probability.  The block length and block count may be any
natural numbers. -/
theorem iidSequenceLaw_measure_forall_blockOscillation
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (width : ℝ) (blocks length : ℕ) :
    iidSequenceLaw ν {increment | ∀ j : Fin blocks,
      blockOscillationEvent width length
        (Combinatorics.Sequence.blockCoordinates (j * length) length increment)} =
      (iidSequenceLaw ν {increment |
        blockOscillationEvent width length
          (Combinatorics.Sequence.blockCoordinates 0 length increment)}) ^ blocks := by
  let blockMap : Fin blocks → (ℕ → ℝ) → (Fin length → ℝ) := fun j =>
    Combinatorics.Sequence.blockCoordinates (j * length) length
  let allBlocks : (ℕ → ℝ) → (Fin blocks → Fin length → ℝ) := fun increment j =>
    blockMap j increment
  let oneBlock : Set (Fin length → ℝ) := blockOscillationEvent width length
  let productSet : Set (Fin blocks → Fin length → ℝ) :=
    Set.univ.pi fun _ : Fin blocks => oneBlock
  have hblockMeasurable (j : Fin blocks) : Measurable (blockMap j) :=
    measurable_blockCoordinates (j * length) length
  have hallBlocksMeasurable : Measurable allBlocks := by
    rw [measurable_pi_iff]
    exact fun j => (hblockMeasurable j).comp measurable_id
  have hindep := iIndepFun_consecutiveBlockCoordinates ν blocks length
  have hmap : (iidSequenceLaw ν).map allBlocks =
      Measure.pi fun j : Fin blocks => (iidSequenceLaw ν).map (blockMap j) :=
    (iIndepFun_iff_map_fun_eq_pi_map
      (fun j => (hblockMeasurable j).aemeasurable)).mp hindep
  have hproductSet : MeasurableSet productSet :=
    MeasurableSet.pi Set.countable_univ fun _ _ =>
      measurableSet_blockOscillationEvent width length
  have hevent : {increment : ℕ → ℝ | ∀ j : Fin blocks,
      blockOscillationEvent width length (blockMap j increment)} =
      allBlocks ⁻¹' productSet := by
    ext increment
    simp only [Set.mem_preimage, productSet, Set.mem_pi, Set.mem_univ,
      true_implies, allBlocks, blockMap, oneBlock, blockOscillationEvent,
      Set.mem_ofPred_eq]
    rfl
  have hshift (j : Fin blocks) :
      (iidSequenceLaw ν).map (blockMap j) oneBlock =
        (iidSequenceLaw ν).map (Combinatorics.Sequence.blockCoordinates 0 length) oneBlock := by
    exact congrArg (fun measure : Measure (Fin length → ℝ) => measure oneBlock)
      (iidSequenceLaw_map_blockCoordinates ν (j * length) length)
  calc
    _ = (iidSequenceLaw ν).map allBlocks productSet := by
      rw [hevent]
      exact (Measure.map_apply hallBlocksMeasurable hproductSet).symm
    _ = (Measure.pi fun j : Fin blocks =>
          (iidSequenceLaw ν).map (blockMap j)) productSet := by rw [hmap]
    _ = ∏ j : Fin blocks,
          (iidSequenceLaw ν).map (blockMap j) oneBlock := by
      change (Measure.pi fun j : Fin blocks =>
          (iidSequenceLaw ν).map (blockMap j))
        (Set.univ.pi fun _ : Fin blocks => oneBlock) = _
      rw [Measure.pi_pi]
    _ = ∏ _j : Fin blocks,
          (iidSequenceLaw ν).map (Combinatorics.Sequence.blockCoordinates 0 length) oneBlock := by
      apply Finset.prod_congr rfl
      intro j hj
      exact hshift j
    _ = ((iidSequenceLaw ν).map (Combinatorics.Sequence.blockCoordinates 0 length) oneBlock) ^ blocks := by
      simp
    _ = _ := by
      congr 1
      rw [Measure.map_apply (measurable_blockCoordinates 0 length)
        (measurableSet_blockOscillationEvent width length)]
      rfl

/-- A horizontal tube forces every increment block covered by the chosen
partition to have oscillation no greater than the tube width.  Combined with
block independence, this gives the discrete horizontal upper inequality from
Mogulskii's block lemma, including an arbitrary incomplete tail. -/
theorem horizontalTubeProbability_le_pow_blockOscillation_of_blockCover
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {a width : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hwidth : 0 ≤ width)
    (blocks length horizon : ℕ) (hcover : blocks * length ≤ horizon) :
    horizontalTubeProbability (iidSequenceLaw ν) a width
        horizon ≤
      (iidSequenceLaw ν {increment |
        blockOscillationEvent width length
          (Combinatorics.Sequence.blockCoordinates 0 length increment)}) ^ blocks := by
  have hzero : -a * width ≤ 0 ∧ 0 ≤ (1 - a) * width := by
    constructor
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hwidth
    · exact mul_nonneg (by linarith) hwidth
  have hposition (increment : ℕ → ℝ)
      (htube : InHorizontalTube a width horizon increment)
      (time : ℕ) (htime : time ≤ horizon) :
      AdditivePath.displacement time increment ∈ Set.Icc (-a * width) ((1 - a) * width) := by
    cases time with
    | zero => simpa using hzero
    | succ time =>
        have htime' : time < horizon := by omega
        have h := htube ⟨time, htime'⟩
        simpa [InHorizontalTube, Set.mem_Icc] using h
  have hsubset :
      {increment : ℕ → ℝ |
        InHorizontalTube a width horizon increment} ⊆
      {increment : ℕ → ℝ | ∀ j : Fin blocks,
        blockOscillationEvent width length
          (Combinatorics.Sequence.blockCoordinates (j * length) length increment)} := by
    intro increment htube j
    change OscillationBounded
      (fun time : Fin (length + 1) =>
        Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates (j * length) length increment) time) width
    intro i k
    have htime (offset : Fin (length + 1)) :
      j * length + (offset : ℕ) ≤ horizon := by
      have hoffset : (offset : ℕ) ≤ length :=
        Nat.le_of_lt_succ offset.isLt
      calc
        j * length + (offset : ℕ) ≤ j * length + length :=
          Nat.add_le_add_left hoffset _
        _ = (j + 1) * length := by simp [Nat.succ_mul]
        _ ≤ horizon := by
          calc
            (j + 1) * length ≤ blocks * length :=
              Nat.mul_le_mul_right length (Nat.succ_le_iff.mpr j.isLt)
            _ ≤ horizon := hcover
    have hvalue (offset : Fin (length + 1)) :
        Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates (j * length) length increment) offset =
          AdditivePath.displacement (j * length + offset) increment -
            AdditivePath.displacement (j * length) increment := by
      rw [partialSum_blockCoordinates]
      have h := AdditivePath.displacement_add_eq_add_blockSum
        (j * length) (offset : ℕ) increment
      linarith
    have hi := hposition increment htube (j * length + (i : ℕ)) (htime i)
    have hk := hposition increment htube (j * length + (k : ℕ)) (htime k)
    change |Fin.partialSum
        (Combinatorics.Sequence.blockCoordinates (j * length) length increment) i -
      Fin.partialSum (Combinatorics.Sequence.blockCoordinates (j * length) length increment) k| ≤ width
    rw [hvalue i, hvalue k]
    have hupper :
        AdditivePath.displacement (j * length + (i : ℕ)) increment -
          AdditivePath.displacement (j * length + (k : ℕ)) increment ≤ width := by
      calc
        _ ≤ (1 - a) * width - (-a * width) := sub_le_sub hi.2 hk.1
        _ = width := by ring
    have hlower :
        -(width) ≤ AdditivePath.displacement (j * length + (i : ℕ)) increment -
          AdditivePath.displacement (j * length + (k : ℕ)) increment := by
      calc
        -(width) = (-a * width) - ((1 - a) * width) := by ring
        _ ≤ AdditivePath.displacement (j * length + i) increment -
            AdditivePath.displacement (j * length + k) increment := sub_le_sub hi.1 hk.2
    have habs : |AdditivePath.displacement (j * length + (i : ℕ)) increment -
        AdditivePath.displacement (j * length + (k : ℕ)) increment| ≤ width :=
      abs_le.mpr ⟨hlower, hupper⟩
    have hcancel :
        |(AdditivePath.displacement (j * length + i) increment -
              AdditivePath.displacement (j * length) increment) -
          (AdditivePath.displacement (j * length + k) increment -
              AdditivePath.displacement (j * length) increment)| =
          |AdditivePath.displacement (j * length + i) increment -
            AdditivePath.displacement (j * length + k) increment| := by
      congr 1
      ring
    rw [hcancel]
    exact habs
  calc
    horizontalTubeProbability (iidSequenceLaw ν) a width horizon =
      iidSequenceLaw ν {increment |
        InHorizontalTube a width horizon increment} := rfl
    _ ≤ iidSequenceLaw ν {increment : ℕ → ℝ | ∀ j : Fin blocks,
          blockOscillationEvent width length
            (Combinatorics.Sequence.blockCoordinates (j * length) length increment)} :=
      measure_mono hsubset
    _ = (iidSequenceLaw ν {increment |
          blockOscillationEvent width length
            (Combinatorics.Sequence.blockCoordinates 0 length increment)}) ^ blocks :=
      iidSequenceLaw_measure_forall_blockOscillation ν width blocks length

/-- The preceding block inequality with the maximal number of complete
blocks.  The final incomplete segment is ignored, exactly as in the discrete
block comparison. -/
theorem horizontalTubeProbability_le_pow_blockOscillation
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {a width : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hwidth : 0 ≤ width)
    (length horizon : ℕ) :
    horizontalTubeProbability (iidSequenceLaw ν) a width horizon ≤
      (iidSequenceLaw ν {increment |
        blockOscillationEvent width length
          (Combinatorics.Sequence.blockCoordinates 0 length increment)}) ^ (horizon / length) := by
  exact horizontalTubeProbability_le_pow_blockOscillation_of_blockCover
    ν ha0 ha1 hwidth (horizon / length) length horizon
    (Nat.div_mul_le_self horizon length)

/-- A block lower bound is iterable only when the block returns to the same
measurable core from which it starts.  Iterating this return kernel gives a
lower bound for the horizontal-tube probability at the concatenated horizon.
This is the abstract kernel form of the lower block iteration in Mogulskii's
discrete lemma; the separate task is to establish the one-block row bound. -/
theorem horizontalTubeProbability_ge_pow_returnBlock
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {a width : ℝ}
    (returnSet : Set ℝ) (hreturn : MeasurableSet returnSet)
    (hzero : (0 : ℝ) ∈ returnSet)
    (lowerBound : ENNReal) (blocks length : ℕ)
    (hblock : ∀ x : returnSet,
      lowerBound ≤ Kernel.returnKernel
        (killedIncrementKernel ν
          (Set.Icc (width * (-a)) (width * (1 - a))) measurableSet_Icc)
        returnSet hreturn length x (Set.univ : Set returnSet)) :
    lowerBound ^ blocks ≤
      horizontalTubeProbability (iidSequenceLaw ν) a width
        (blocks * length) := by
  let K := killedIncrementKernel ν
    (Set.Icc (width * (-a)) (width * (1 - a))) measurableSet_Icc
  let R := Kernel.returnKernel K returnSet hreturn length
  let start : returnSet := ⟨0, hzero⟩
  have hrow : ∀ x : returnSet,
      lowerBound ≤ Kernel.remainingMass R 1 x := by
    intro x
    simpa [Kernel.remainingMass, R, K] using hblock x
  have hpower : lowerBound ^ blocks ≤ Kernel.remainingMass R blocks start := by
    simpa only [Nat.mul_one] using
      Kernel.pow_le_remainingMass_mul R 1 blocks start lowerBound hrow
  have hambient : Kernel.remainingMass R blocks start ≤
      Kernel.remainingMass K (blocks * length) (start : ℝ) := by
    simpa [R, K] using Kernel.remainingMass_returnKernel_le K returnSet hreturn
      length blocks start
  have hscaled := hpower.trans hambient
  simpa [start, K] using hscaled.trans_eq
    (remainingMass_killedIncrementKernel_scaled_Icc_eq_horizontalTubeProbability
      ν a width (blocks * length))

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

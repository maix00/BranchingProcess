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
public import Mathlib.Algebra.Order.Floor.Semifield

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

/-- The finite-block path has range strictly less than `width`, expressed as
the pairwise strict-distance condition used by the source's class `J₁`. -/
def blockOscillationLTEvent (width : ℝ) (length : ℕ) :
    Set (Fin length → ℝ) :=
  {increments | ∀ i j : Fin (length + 1),
    |Fin.partialSum increments i - Fin.partialSum increments j| < width}

/-- The strict finite-block range event is measurable. -/
theorem measurableSet_blockOscillationLTEvent (width : ℝ) (length : ℕ) :
    MeasurableSet (blockOscillationLTEvent width length) := by
  rw [show blockOscillationLTEvent width length =
      ⋂ i : Fin (length + 1), ⋂ j : Fin (length + 1),
        {increments : Fin length → ℝ |
          |Fin.partialSum increments i - Fin.partialSum increments j| <
            width} by
    ext increments
    simp [blockOscillationLTEvent]]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => by
    have hdiff : Measurable (fun increments : Fin length → ℝ =>
        Fin.partialSum increments i - Fin.partialSum increments j) :=
      (measurable_partialSum i).sub (measurable_partialSum j)
    exact measurableSet_Iio.preimage
      (continuous_abs.measurable.comp hdiff)

/-- Every one of finitely many independent equal-length IID increment blocks
has range strictly less than `width` with probability equal to the
corresponding power of the one-block probability. -/
theorem iidSequenceLaw_measure_forall_blockOscillationLT
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (width : ℝ) (blocks length : ℕ) :
    iidSequenceLaw ν {increment | ∀ j : Fin blocks,
      blockOscillationLTEvent width length
        (Combinatorics.Sequence.blockCoordinates (j * length) length increment)} =
      (iidSequenceLaw ν {increment |
      blockOscillationLTEvent width length
        (Combinatorics.Sequence.blockCoordinates 0 length increment)}) ^ blocks := by
  change iidSequenceLaw ν {increment : ℕ → ℝ | ∀ j : Fin blocks,
      Combinatorics.Sequence.blockCoordinates (j * length) length increment ∈
        blockOscillationLTEvent width length} = _
  exact iidSequenceLaw_measure_forall_consecutiveBlockEvent ν blocks length
    (blockOscillationLTEvent width length)
    (measurableSet_blockOscillationLTEvent width length)

/-- The probability that every one of a finite family of consecutive IID
increment blocks has oscillation at most `width` is the corresponding power
of the one-block probability. The block-event product formula lives in the
generic random-walk block-law layer. -/
theorem iidSequenceLaw_measure_forall_blockOscillation
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (width : ℝ) (blocks length : ℕ) :
    iidSequenceLaw ν {increment | ∀ j : Fin blocks,
      blockOscillationEvent width length
        (Combinatorics.Sequence.blockCoordinates (j * length) length increment)} =
      (iidSequenceLaw ν {increment |
      blockOscillationEvent width length
        (Combinatorics.Sequence.blockCoordinates 0 length increment)}) ^ blocks := by
  change iidSequenceLaw ν {increment : ℕ → ℝ | ∀ j : Fin blocks,
      Combinatorics.Sequence.blockCoordinates (j * length) length increment ∈
        blockOscillationEvent width length} = _
  exact iidSequenceLaw_measure_forall_consecutiveBlockEvent ν blocks length
    (blockOscillationEvent width length)
    (measurableSet_blockOscillationEvent width length)

/-- Mogulskii's strict path-class comparison: if an IID walk stays in one
open interval through a covered horizon, then every covered block has
strictly smaller range than the interval width. The block events are
independent, so the full-path probability is bounded by the one-block
probability raised to the number of covered blocks. -/
theorem openHorizontalTubeProbability_le_pow_blockOscillationLT_of_blockCover
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {a width : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hwidth : 0 < width)
    (blocks length horizon : ℕ) (hcover : blocks * length ≤ horizon) :
    openHorizontalTubeProbability (iidSequenceLaw ν) a width horizon ≤
      (iidSequenceLaw ν {increment |
        blockOscillationLTEvent width length
          (Combinatorics.Sequence.blockCoordinates 0 length increment)}) ^ blocks := by
  have hzero : -a * width < 0 ∧ 0 < (1 - a) * width := by
    constructor
    · nlinarith [mul_pos ha0 hwidth]
    · nlinarith [mul_pos (show 0 < 1 - a by linarith) hwidth]
  have hposition (increment : ℕ → ℝ)
      (htube : InOpenHorizontalTube a width horizon increment)
      (time : ℕ) (htime : time ≤ horizon) :
      -a * width < AdditivePath.displacement time increment ∧
        AdditivePath.displacement time increment < (1 - a) * width := by
    cases time with
    | zero => simpa using hzero
    | succ time =>
      have htime' : time < horizon := by omega
      simpa [InOpenHorizontalTube] using htube ⟨time, htime'⟩
  have hsubset :
      {increment : ℕ → ℝ | InOpenHorizontalTube a width horizon increment} ⊆
        {increment : ℕ → ℝ | ∀ j : Fin blocks,
          blockOscillationLTEvent width length
            (Combinatorics.Sequence.blockCoordinates
              (j * length) length increment)} := by
    intro increment htube j
    change ∀ i k : Fin (length + 1),
      |Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates (j * length) length increment) i -
        Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates (j * length) length increment) k| <
            width
    intro i k
    have htime (offset : Fin (length + 1)) :
        j * length + (offset : ℕ) ≤ horizon := by
      have hoffset : (offset : ℕ) ≤ length := Nat.le_of_lt_succ offset.isLt
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
    have hupper :
        AdditivePath.displacement (j * length + (i : ℕ)) increment -
            AdditivePath.displacement (j * length + (k : ℕ)) increment < width := by
      calc
        _ < (1 - a) * width - (-a * width) := by linarith [hi.2, hk.1]
        _ = width := by ring
    have hlower :
        -(width) < AdditivePath.displacement (j * length + (i : ℕ)) increment -
            AdditivePath.displacement (j * length + (k : ℕ)) increment := by
      have hreverse :
          AdditivePath.displacement (j * length + (k : ℕ)) increment -
            AdditivePath.displacement (j * length + (i : ℕ)) increment < width := by
        calc
          _ < (1 - a) * width - (-a * width) := by linarith [hk.2, hi.1]
          _ = width := by ring
      linarith [hreverse]
    have hcancel :
        |(AdditivePath.displacement (j * length + (i : ℕ)) increment -
            AdditivePath.displacement (j * length) increment) -
          (AdditivePath.displacement (j * length + (k : ℕ)) increment -
            AdditivePath.displacement (j * length) increment)| =
          |AdditivePath.displacement (j * length + (i : ℕ)) increment -
            AdditivePath.displacement (j * length + (k : ℕ)) increment| := by
      congr 1
      ring
    rw [hvalue i, hvalue k, hcancel]
    exact abs_lt.mpr ⟨hlower, hupper⟩
  calc
    openHorizontalTubeProbability (iidSequenceLaw ν) a width horizon =
        iidSequenceLaw ν {increment |
          InOpenHorizontalTube a width horizon increment} := rfl
    _ ≤ iidSequenceLaw ν {increment : ℕ → ℝ | ∀ j : Fin blocks,
          blockOscillationLTEvent width length
            (Combinatorics.Sequence.blockCoordinates
              (j * length) length increment)} := measure_mono hsubset
    _ = (iidSequenceLaw ν {increment |
          blockOscillationLTEvent width length
            (Combinatorics.Sequence.blockCoordinates 0 length increment)}) ^ blocks :=
      iidSequenceLaw_measure_forall_blockOscillationLT ν width blocks length

/-- The source parameterization of Mogulskii's Lemma 3(c), equation (32):
for `c = length / horizon`, the source block count `⌊c⁻¹⌋₊` is
`horizon / length`. The bound uses the strict source corridor and strict
`J₁` range event. -/
theorem openHorizontalTubeProbability_le_pow_blockOscillationLT_source
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {a width : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hwidth : 0 < width)
    (horizon length : ℕ) (hhorizon : 0 < horizon)
    (hlength : 0 < length) :
    openHorizontalTubeProbability (iidSequenceLaw ν) a width horizon ≤
      (iidSequenceLaw ν {increment |
        blockOscillationLTEvent width length
          (Combinatorics.Sequence.blockCoordinates 0 length increment)}) ^
        ⌊((length : ℝ) / (horizon : ℝ))⁻¹⌋₊ := by
  have hcount : ⌊((length : ℝ) / (horizon : ℝ))⁻¹⌋₊ = horizon / length := by
    have hquotient : ((length : ℝ) / (horizon : ℝ))⁻¹ =
        (horizon : ℝ) / (length : ℝ) := by
      field_simp [Nat.cast_ne_zero.mpr hhorizon.ne',
        Nat.cast_ne_zero.mpr hlength.ne']
    rw [hquotient, Nat.floor_div_eq_div]
  rw [hcount]
  exact openHorizontalTubeProbability_le_pow_blockOscillationLT_of_blockCover
    ν ha0 ha1 hwidth (horizon / length) length horizon
    (Nat.div_mul_le_self horizon length)

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

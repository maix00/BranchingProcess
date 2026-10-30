/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Probability.Process.RandomWalk.Path.Block.Law.Basic
public import Probability.Process.RandomWalk.Path.Block.Oscillation
public import Probability.Process.RandomWalk.Path.Block.Partition.Basic
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Basic
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core

import Probability.Sequence.IID.Blocks.Consecutive

/-!
# Horizontal-tube upper bounds from finite block oscillation

## Public declarations

For the tube event $T_{a,w,N}$ and the length-$m$ block oscillation events
$J_{w,m}$ and $J^\circ_{w,m}$, these declarations give finite-time bounds
from independent consecutive blocks:

- `openHorizontalTubeProbability_le_pow_blockOscillationLT_of_blockCover`:
  if $qm\le N$, then $\mathbb P(T^\circ_{a,w,N})\le
  \mathbb P(J^\circ_{w,m})^q$.
- `openHorizontalTubeProbability_le_pow_blockOscillationLT_of_completeBlocks`:
  the same estimate with the maximal complete-block count
  $q=\lfloor N/m\rfloor$.
- `horizontalTubeProbability_le_pow_blockOscillation_of_blockCover` and
  `horizontalTubeProbability_le_pow_blockOscillation`:
  $\mathbb P(T_{a,w,N})\le\mathbb P(J_{w,m})^q$, for a supplied block
  cover or the maximal complete-block count.
- `horizontalTubeProbability_le_exp_of_blockOscillationProbability`:
  a one-block bound $\mathbb P(J_{w,m})\le e^{-dm/w^2}$ gives
  $\mathbb P(T_{a,w,N})\le e^{r-dN/w^2}$ when $dm/w^2\le r$.

The independent-block inequalities are used in Mogul'skii, “Small deviations
in the sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4)
(1974), 755–765; English translation, “Small Deviations in a Space of
Trajectories,” *Theory of Probability and Its Applications* 19(4) (1975),
726–736, DOI 10.1137/1119081, Lemma 3(c), equation (32). The statements use
only an IID increment law and finite-time block geometry.
-/

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk
open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

/-- If an IID walk stays in one open interval through a covered horizon,
then every covered block has strictly smaller range than the interval width.
Independence of the block events gives the power bound. -/
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
      iidSequenceLaw_measure_forall_consecutiveBlockEvent ν blocks length
        (blockOscillationLTEvent width length)
        (measurableSet_blockOscillationLTEvent width length)

/-- The maximal complete-block bound follows by taking `horizon / length`
blocks. The final incomplete segment contributes no condition to the block
product estimate. -/
theorem openHorizontalTubeProbability_le_pow_blockOscillationLT_of_completeBlocks
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
    change Metric.OscillationBounded
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
      iidSequenceLaw_measure_forall_consecutiveBlockEvent ν blocks length
        (blockOscillationEvent width length)
        (measurableSet_blockOscillationEvent width length)

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

/-- Iterate a one-block oscillation estimate along a horizontal tube. The
remainder parameter absorbs the cost of the incomplete last block. -/
theorem horizontalTubeProbability_le_exp_of_blockOscillationProbability
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {a width d remainder : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hwidth : 0 < width) (hd : 0 < d)
    (length horizon : ℕ) (hlength : 0 < length)
    (hblockRemainder : d * ((length : ℝ) / width ^ 2) ≤ remainder)
    (hblock : iidSequenceLaw ν {increment : ℕ → ℝ |
      blockOscillationEvent width length
        (Combinatorics.Sequence.blockCoordinates 0 length increment)} ≤
      ENNReal.ofReal (Real.exp (-d * ((length : ℝ) / width ^ 2)))) :
    horizontalTubeProbability (iidSequenceLaw ν) a width horizon ≤
      ENNReal.ofReal (Real.exp
        (remainder - d * ((horizon : ℝ) / width ^ 2))) := by
  let blocks := horizon / length
  let cost : ℝ := d / width ^ 2
  have hcost : 0 < cost := by
    dsimp [cost]
    exact div_pos hd (sq_pos_of_pos hwidth)
  have hblockRemainder' : cost * (length : ℝ) ≤ remainder := by
    dsimp [cost]
    have hden : width ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hwidth)
    rw [div_mul_eq_mul_div, mul_comm]
    convert hblockRemainder using 1
    field_simp [hden]
  have hdecomp : blocks * length + horizon % length = horizon := by
    dsimp [blocks]
    calc
      horizon / length * length + horizon % length =
          length * (horizon / length) + horizon % length := by rw [Nat.mul_comm]
      _ = horizon := Nat.div_add_mod horizon length
  have hrem : horizon % length < length := Nat.mod_lt _ hlength
  have hcoverageNat : horizon ≤ blocks * length + length := by omega
  have hcoverage : (horizon : ℝ) ≤ (blocks : ℝ) * length + length := by
    exact_mod_cast hcoverageNat
  have hcostCoverage := mul_le_mul_of_nonneg_left hcoverage hcost.le
  have htotalCost : cost * (horizon : ℝ) ≤
      cost * ((blocks : ℝ) * length) + remainder := by
    calc
      cost * (horizon : ℝ) ≤ cost * ((blocks : ℝ) * length + length) :=
        hcostCoverage
      _ = cost * ((blocks : ℝ) * length) + cost * length := by ring
      _ ≤ cost * ((blocks : ℝ) * length) + remainder := by
        calc
          cost * ((blocks : ℝ) * length) + cost * length =
              cost * length + cost * ((blocks : ℝ) * length) := by ring
          _ ≤ remainder + cost * ((blocks : ℝ) * length) :=
            add_le_add_left hblockRemainder' _
          _ = cost * ((blocks : ℝ) * length) + remainder := by ring
  have hexponent :
      (-d * ((length : ℝ) / width ^ 2)) * (blocks : ℝ) ≤
        remainder - d * ((horizon : ℝ) / width ^ 2) := by
    have hlengthCost : d * ((length : ℝ) / width ^ 2) = cost * length := by
      dsimp [cost]
      field_simp [ne_of_gt hwidth]
    have hhorizonCost : d * ((horizon : ℝ) / width ^ 2) =
        cost * (horizon : ℝ) := by
      dsimp [cost]
      field_simp [ne_of_gt hwidth]
    have hnegLength : -d * ((length : ℝ) / width ^ 2) =
        -(cost * length) := by
      calc
        -d * ((length : ℝ) / width ^ 2) =
            -(d * ((length : ℝ) / width ^ 2)) := by ring
        _ = -(cost * length) := by rw [hlengthCost]
    rw [hnegLength, hhorizonCost]
    have hcostBlocks :
        cost * ((blocks : ℝ) * length) =
          (cost * length) * (blocks : ℝ) := by ring
    nlinarith [htotalCost, hcostBlocks]
  have hpow := horizontalTubeProbability_le_pow_blockOscillation
    ν ha0 ha1 hwidth.le length horizon
  have hpowBlock :
      (iidSequenceLaw ν {increment : ℕ → ℝ |
        blockOscillationEvent width length
          (Combinatorics.Sequence.blockCoordinates 0 length increment)}) ^ blocks ≤
        (ENNReal.ofReal (Real.exp (-d * ((length : ℝ) / width ^ 2)))) ^ blocks :=
    pow_le_pow_left' hblock blocks
  have hexpPow :
      ENNReal.ofReal (Real.exp (-d * ((length : ℝ) / width ^ 2))) ^ blocks =
        ENNReal.ofReal (Real.exp
          ((-d * ((length : ℝ) / width ^ 2)) * (blocks : ℝ))) := by
    rw [← ENNReal.ofReal_pow (Real.exp_nonneg _) blocks,
      ← Real.exp_nat_mul]
    congr 1
    ring
  have hfinalReal := Real.exp_le_exp.mpr hexponent
  have hfinalENN : ENNReal.ofReal (Real.exp
        ((-d * ((length : ℝ) / width ^ 2)) * (blocks : ℝ))) ≤
      ENNReal.ofReal (Real.exp
        (remainder - d * ((horizon : ℝ) / width ^ 2))) :=
    (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _)).2 hfinalReal
  calc
    horizontalTubeProbability (iidSequenceLaw ν) a width horizon ≤
        (iidSequenceLaw ν {increment : ℕ → ℝ |
          blockOscillationEvent width length
            (Combinatorics.Sequence.blockCoordinates 0 length increment)}) ^ blocks := by
      simpa [blocks] using hpow
    _ ≤ (ENNReal.ofReal
        (Real.exp (-d * ((length : ℝ) / width ^ 2)))) ^ blocks := hpowBlock
    _ = ENNReal.ofReal (Real.exp
        ((-d * ((length : ℝ) / width ^ 2)) * (blocks : ℝ))) := hexpPow
    _ ≤ ENNReal.ofReal (Real.exp
        (remainder - d * ((horizon : ℝ) / width ^ 2))) := hfinalENN

end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

end

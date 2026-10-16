/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Partition.Basic
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Basic
public import Probability.Process.RandomWalk.Path.Event.Oscillation
public import Probability.Process.RandomWalk.Path.Block.Law.Basic
public import Probability.Process.RandomWalk.Kernel.Killed.Return.Basic
public import Probability.Process.RandomWalk.Kernel.Killed.Blocking
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
public import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Discrete horizontal block inequalities

Write $T_{a,w,N}$ for the width-$w$ horizontal-tube event, $J_{w,m}$
for the range-at-most-$w$ event on one block of length $m$, and
$J^\circ_{w,m}$ for its strict version. The public declarations are:

- `blockOscillationEvent`, `measurableSet_blockOscillationEvent`,
  `blockOscillationLTEvent`, and `measurableSet_blockOscillationLTEvent`:
  the measurable events $J_{w,m}$ and $J^\circ_{w,m}$.
- `iidSequenceLaw_measure_forall_blockOscillationLT` and
  `iidSequenceLaw_measure_forall_blockOscillation`:
  the event on $q$ disjoint IID blocks has probability
  $\mathbb P(J_{w,m})^q$, also for $J^\circ_{w,m}$.
- `openHorizontalTubeProbability_le_pow_blockOscillationLT_of_blockCover`
  and `openHorizontalTubeProbability_le_pow_blockOscillationLT_source`:
  $\mathbb P(T^\circ_{a,w,N})\le\mathbb P(J^\circ_{w,m})^q$
  whenever $qm\le N$, with the source choice $q=\lfloor N/m\rfloor$
  for $m>0$.
- `iidSequenceLaw_measure_partialSumRangeLT_le_pow_blockOscillationLT_of_blockCover`:
  the same bound for a strict whole-path range event.
- `horizontalTubeProbability_le_pow_blockOscillation_of_blockCover` and
  `horizontalTubeProbability_le_pow_blockOscillation`:
  $\mathbb P(T_{a,w,N})\le\mathbb P(J_{w,m})^q$ for $qm\le N$,
  in particular for $q=\lfloor N/m\rfloor$ when $m>0$.
- `horizontalTubeProbability_le_exp_of_blockOscillationProbability`:
  a one-block bound $\mathbb P(J_{w,m})\le e^{-dm/w^2}$ yields
  $\mathbb P(T_{a,w,N})\le e^{R-dN/w^2}$ with $R\ge dm/w^2$.
- `horizontalTubeProbability_ge_pow_returnBlock`:
  a lower return-kernel mass $p$ on a common core yields
  $p^q\le\mathbb P(T_{a,w,qm})$.

These are the finite-time block comparisons in Mogul'skii,
*Small Deviations in a Space of Trajectories*, Lemma 3(c), equation (32).
They apply to IID increments through disjoint-block independence.


The original bibliography is A. A. Mogul'skii, “Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation, “Small Deviations in a Space of Trajectories,” *Theory of Probability and Its Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081. -/

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

/-- A strict range bound on a whole finite walk forces the same strict range
bound on every complete equal-length increment block. The block events are
independent, so this gives the direct range-event analogue of Lemma 3(c),
without choosing a center for the corridor. -/
theorem iidSequenceLaw_measure_partialSumRangeLT_le_pow_blockOscillationLT_of_blockCover
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (width : ℝ) (blocks length horizon : ℕ)
    (hcover : blocks * length ≤ horizon) :
    partialSumRangeOscillationLTProbability (iidSequenceLaw ν) width horizon ≤
      (iidSequenceLaw ν {increment |
        blockOscillationLTEvent width length
          (Combinatorics.Sequence.blockCoordinates 0 length increment)}) ^ blocks := by
  change iidSequenceLaw ν {increment | ∀ i j : Fin (horizon + 1),
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
      iidSequenceLaw_measure_forall_blockOscillationLT ν width blocks length

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

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Analysis.Asymptotics.Scale.Block.Length
public import Probability.Process.RandomWalk.Path.Representation.Cadlag
public import Probability.Process.RandomWalk.Path.Block.Partition.Basic
public import Probability.Process.RandomWalk.Path.Block.Law.Oscillation
public import Probability.Sequence.IID.Basic
public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Basic
public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Boundary.Partition
import all Probability.Process.RandomWalk.Path.Block.Partition.Range

/-!
# Random-walk partitions of step corridors

Let $t_i$ be the common partition grid of step boundaries $U,L$, and put
$F_n(t)=\lfloor nt\rfloor$ and $q_i(n)=F_n(t_{i+1})-F_n(t_i)$. The finite-cell
range comparison is valid for every pair of `StepBoundary` objects and every
IID real increment law. It has no moment, stability, or asymptotic-scale
hypothesis. This general interface is used in the discrete partition argument
of A. A. Mogul'skii, Theorem 3, Section 4, p. 764, “Small deviations in the
sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755--765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081.

## Public declarations

The declarations in `ProbabilityTheory.RandomWalk.Path.Block.Partition.StepCorridor`
are:

- `commonPartitionFloorTimeIndex`: $F_n(t)=\lfloor nt\rfloor$.
- `commonPartitionCellStepLength`: $q_i(n)$, the number of integer steps in
  the floor-rounded cell $[t_i,t_{i+1})$.
- `commonPartitionCellStepLengths`: the sequence equal to $q_i(n)$ on valid
  cells and $0$ afterwards.
- `commonPartitionCellStepLength_le`: $q_i(n)\le n$.
- `commonPartitionFloorTimeIndex_mono`: $s\le t$ implies $F_n(s)\le F_n(t)$.
- `commonPartitionFloorTimeIndex_le_n_sub_one_of_lt_top`: if $t<1$, then
  $F_n(t)\le n-1$.
- `blockStart_commonPartitionCellStepLengths`:
  $\sum_{j<i}q_j(n)=F_n(t_i)$.
- `tendsto_commonPartitionCellRangeHorizon_div_nat`:
  $(q_i(n)-1)/n\to t_{i+1}-t_i$, the number of constrained positions in the
  half-open cell, normalized by $n$.
- `tendsto_commonPartitionCellStepLength_div_nat`:
  $q_i(n)/n\to t_{i+1}-t_i$.
- `eventually_commonPartitionCellStepLength_pos`: each fixed nonempty grid
  cell has $q_i(n)>0$ eventually.
- `exists_commonPartitionCellTime_floor_eq`: if $n>0$, $t_i<t_{i+1}$, and
  $F_n(t_i)=a$, $F_n(t_{i+1})=b$, every integer $a\le j<b$ is $F_n(t)$ for
  some $t\in[t_i,t_{i+1})$.
- `normalizedStepCorridor_subset_selectedHalfOpenCellPositions`: when the
  right traces on selected cells equal finite bounds $\ell_i,u_i$, membership
  of the normalized step path in the global corridor implies
  $s_n\ell_i<D_{F_n(t_i)+k}<s_nu_i$ for every selected $i$ and $k<q_i(n)$.
- `iidSequenceLaw_normalizedStepCorridor_le_selectedCellRangeProduct`: under
  the same boundary equalities, positive $n,s_n$, and $q_i(n)>0$ on a finite
  selected set $S$, the IID corridor probability is at most
  $\prod_{i\in S}\pi_{s_n(u_i-\ell_i)}(q_i(n)-1)$, where $\pi_w(r)$ is the
  probability that the partial-sum range of $r$ increments is less than $w$.

The floor-rounded partition connects half-open cells to the right-continuous
normalized random-walk path. The API uses the existing `StepBoundary` common
grid, normalized step-path representation, and IID range product bound
without duplicating those interfaces.
-/

open Skorokhod.PathClass.StepCorridor

@[expose] public section

open Filter MeasureTheory

namespace ProbabilityTheory.RandomWalk.Path.Block.Partition.StepCorridor

open Skorokhod.PathClass.StepCorridor

/-- The integer position observed by the normalized step path at time `t`. -/
noncomputable def commonPartitionFloorTimeIndex (n : ℕ) (t : unitInterval) : ℕ :=
  ⌊(n : ℝ) * (t : ℝ)⌋₊

/-- The number of integer positions in one floor-rounded common-partition
cell. -/
noncomputable def commonPartitionCellStepLength (n : ℕ) (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) : ℕ :=
  commonPartitionFloorTimeIndex n
      (StepBoundary.commonPartitionGrid upper lower (i.val + 1)) -
    commonPartitionFloorTimeIndex n
      (StepBoundary.commonPartitionGrid upper lower i.val)

/-- A partition cell contains at most the first `n` grid steps of the
unit interval. -/
theorem commonPartitionCellStepLength_le (n : ℕ) (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    commonPartitionCellStepLength n upper lower i ≤ n := by
  let right := StepBoundary.commonPartitionGrid upper lower (i.val + 1)
  have hright : (right : ℝ) ≤ 1 := right.property.2
  have hprod : (n : ℝ) * (right : ℝ) ≤ n := by
    calc
      (n : ℝ) * (right : ℝ) ≤ (n : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hright (Nat.cast_nonneg n)
      _ = n := by ring
  have hfloor : (commonPartitionFloorTimeIndex n right : ℝ) ≤ n := by
    change (⌊(n : ℝ) * (right : ℝ)⌋₊ : ℝ) ≤ (n : ℝ)
    calc
      (⌊(n : ℝ) * (right : ℝ)⌋₊ : ℝ) ≤ (n : ℝ) * (right : ℝ) :=
        Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) right.property.1)
      _ ≤ n := hprod
  have hfloorNat : commonPartitionFloorTimeIndex n right ≤ n := by
    exact_mod_cast hfloor
  calc
    commonPartitionCellStepLength n upper lower i ≤
        commonPartitionFloorTimeIndex n right := by
      simp [commonPartitionCellStepLength, commonPartitionFloorTimeIndex, right]
    _ ≤ n := hfloorNat

/-- Extend the finite family of cell lengths by zero outside the partition;
`Combinatorics.Sequence.blockStart` can then be used on the finite index set. -/
noncomputable def commonPartitionCellStepLengths (n : ℕ) (upper lower : StepBoundary) :
    ℕ → ℕ := fun j =>
  if _hj : j < (StepBoundary.commonKnots upper lower).card - 1 then
    commonPartitionFloorTimeIndex n
        (StepBoundary.commonPartitionGrid upper lower (j + 1)) -
      commonPartitionFloorTimeIndex n
        (StepBoundary.commonPartitionGrid upper lower j)
  else 0

theorem commonPartitionFloorTimeIndex_mono (n : ℕ) {s t : unitInterval}
    (hst : s ≤ t) :
    commonPartitionFloorTimeIndex n s ≤ commonPartitionFloorTimeIndex n t := by
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hst) (Nat.cast_nonneg n)

/-- Before the terminal time, the floor-time index is at most `n - 1`. -/
theorem commonPartitionFloorTimeIndex_le_n_sub_one_of_lt_top
    (n : ℕ) {t : unitInterval} (ht : t < ⊤) :
    commonPartitionFloorTimeIndex n t ≤ n - 1 := by
  by_cases hn : n = 0
  · subst n
    simp [commonPartitionFloorTimeIndex]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hmul : (n : ℝ) * (t : ℝ) < (n : ℝ) := by
      have htval : (t : ℝ) < 1 := by
        by_contra hnot
        have heq : (t : ℝ) = 1 := le_antisymm t.property.2 (le_of_not_gt hnot)
        exact (ne_of_lt ht) (Subtype.ext heq)
      have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
      calc
        (n : ℝ) * (t : ℝ) < (n : ℝ) * 1 :=
          mul_lt_mul_of_pos_left htval hnreal
        _ = (n : ℝ) := by ring
    have hfloorNat : commonPartitionFloorTimeIndex n t < n := by
      change ⌊(n : ℝ) * (t : ℝ)⌋₊ < n
      exact (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg n) t.property.1)).2 hmul
    omega

/-- The cumulative lengths of the floor-rounded cells recover the floor index
at the corresponding common partition knot. -/
theorem blockStart_commonPartitionCellStepLengths
    (n : ℕ) (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    Combinatorics.Sequence.blockStart (commonPartitionCellStepLengths n upper lower) i.val =
      commonPartitionFloorTimeIndex n
        (StepBoundary.commonPartitionGrid upper lower i.val) := by
  have hprefix (j : ℕ) (hj : j ≤
      (StepBoundary.commonKnots upper lower).card - 1) :
      Combinatorics.Sequence.blockStart (commonPartitionCellStepLengths n upper lower) j =
        commonPartitionFloorTimeIndex n
          (StepBoundary.commonPartitionGrid upper lower j) := by
    induction j with
    | zero =>
        simp [commonPartitionFloorTimeIndex,
          StepBoundary.commonPartitionGrid_zero]
    | succ j ih =>
        have hj' : j ≤ (StepBoundary.commonKnots upper lower).card - 1 := by omega
        have hjlt : j < (StepBoundary.commonKnots upper lower).card - 1 := by omega
        rw [Combinatorics.Sequence.blockStart_succ, ih hj']
        have hlen : commonPartitionCellStepLengths n upper lower j =
            commonPartitionFloorTimeIndex n
                (StepBoundary.commonPartitionGrid upper lower (j + 1)) -
              commonPartitionFloorTimeIndex n
                (StepBoundary.commonPartitionGrid upper lower j) := by
          simp [commonPartitionCellStepLengths, hjlt]
        rw [hlen]
        have hgrid : StepBoundary.commonPartitionGrid upper lower j ≤
            StepBoundary.commonPartitionGrid upper lower (j + 1) :=
          StepBoundary.monotone_commonPartitionGrid upper lower (Nat.le_succ j)
        have hmono := commonPartitionFloorTimeIndex_mono n hgrid
        simpa [Nat.add_comm] using Nat.sub_add_cancel hmono
  exact hprefix i.val (Nat.le_of_lt i.isLt)

/-- The number of positions constrained in a half-open floor-rounded cell,
minus the unrestricted terminal position, has the cell's macroscopic time
length. -/
theorem tendsto_commonPartitionCellRangeHorizon_div_nat
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    Tendsto
      (fun n =>
        ((commonPartitionCellStepLength n upper lower i - 1 : ℕ) : ℝ) /
          (n : ℝ)) atTop
      (nhds ((StepBoundary.commonPartitionGrid upper lower (i.val + 1) : unitInterval) -
        StepBoundary.commonPartitionGrid upper lower i.val)) := by
  let left := (StepBoundary.commonPartitionGrid upper lower i.val : ℝ)
  let right := (StepBoundary.commonPartitionGrid upper lower (i.val + 1) : ℝ)
  have hleft : 0 ≤ left := (StepBoundary.commonPartitionGrid upper lower i.val).property.1
  have hle : left < right := by
    exact_mod_cast StepBoundary.commonPartitionGrid_strictSucc upper lower i.val i.isLt
  have h := Asymptotics.tendsto_floorSegmentLength_sub_one_div_nat hleft hle
  simpa [left, right, commonPartitionCellStepLength,
    commonPartitionFloorTimeIndex, Asymptotics.floorBlockLength] using h

/-- The full floor-rounded number of steps in one common partition cell has
the cell's macroscopic time length. -/
theorem tendsto_commonPartitionCellStepLength_div_nat
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    Tendsto
      (fun n => (commonPartitionCellStepLength n upper lower i : ℝ) /
        (n : ℝ)) atTop
      (nhds ((StepBoundary.commonPartitionGrid upper lower (i.val + 1) : unitInterval) -
        StepBoundary.commonPartitionGrid upper lower i.val)) := by
  let left := (StepBoundary.commonPartitionGrid upper lower i.val : ℝ)
  let right := (StepBoundary.commonPartitionGrid upper lower (i.val + 1) : ℝ)
  have hleft : 0 ≤ left := (StepBoundary.commonPartitionGrid upper lower i.val).property.1
  have hle : left < right := by
    exact_mod_cast StepBoundary.commonPartitionGrid_strictSucc upper lower i.val i.isLt
  have h := Asymptotics.tendsto_floorSegmentLength_div_nat hleft (le_of_lt hle)
  simpa [left, right, commonPartitionCellStepLength,
    commonPartitionFloorTimeIndex, Asymptotics.floorBlockLength] using h

/-- Every fixed common partition cell eventually contains at least one walk
step. -/
theorem eventually_commonPartitionCellStepLength_pos
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    ∀ᶠ n : ℕ in atTop, 0 < commonPartitionCellStepLength n upper lower i := by
  have hratio := tendsto_commonPartitionCellStepLength_div_nat upper lower i
  have hratioPos : ∀ᶠ n in atTop,
      0 < (commonPartitionCellStepLength n upper lower i : ℝ) / (n : ℝ) :=
    hratio.eventually (Ioi_mem_nhds (sub_pos.mpr (by
      exact_mod_cast StepBoundary.commonPartitionGrid_strictSucc
        upper lower i.val i.isLt)))
  filter_upwards [hratioPos, eventually_gt_atTop (0 : ℕ)] with n hratio hn
  by_contra hzero
  have hlenZero : commonPartitionCellStepLength n upper lower i = 0 :=
    Nat.eq_zero_of_not_pos hzero
  simp [hlenZero] at hratio

/-- Every integer index between the two rounded endpoints of a positive
partition cell is attained by the right-continuous step path at some time in
that half-open cell. -/
theorem exists_commonPartitionCellTime_floor_eq
    {n start stop j : ℕ} (hn : 0 < n)
    {left right : unitInterval}
    (hleft : commonPartitionFloorTimeIndex n left = start)
    (hright : commonPartitionFloorTimeIndex n right = stop)
    (hle : left < right) (hstart : start ≤ j) (hstop : j < stop) :
    ∃ t : unitInterval, left ≤ t ∧ t < right ∧
      commonPartitionFloorTimeIndex n t = j := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hleftReal : (start : ℝ) ≤ (n : ℝ) * (left : ℝ) := by
    change ⌊(n : ℝ) * (left : ℝ)⌋₊ = start at hleft
    rw [← hleft]
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) left.property.1)
  have hleftReal' : (n : ℝ) * (left : ℝ) < (start : ℝ) + 1 := by
    change ⌊(n : ℝ) * (left : ℝ)⌋₊ = start at hleft
    rw [← hleft]
    exact Nat.lt_floor_add_one _
  have hrightReal : (stop : ℝ) ≤ (n : ℝ) * (right : ℝ) := by
    change ⌊(n : ℝ) * (right : ℝ)⌋₊ = stop at hright
    rw [← hright]
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) right.property.1)
  have hjRight : (j : ℝ) < (n : ℝ) * (right : ℝ) := by
    have hstop' : (j : ℝ) < (stop : ℝ) := by exact_mod_cast hstop
    exact hstop'.trans_le hrightReal
  have hjDiv : (j : ℝ) / (n : ℝ) < (right : ℝ) := by
    apply (div_lt_iff₀ hnReal).2
    calc
      (j : ℝ) < (n : ℝ) * (right : ℝ) := hjRight
      _ = (right : ℝ) * (n : ℝ) := mul_comm _ _
  let x : ℝ := left
  let y : ℝ := right
  let z : ℝ := max x ((j : ℝ) / n)
  have hxz : x ≤ z := le_max_left _ _
  have hzy : z < y := max_lt (by exact_mod_cast hle) (by simpa [y] using hjDiv)
  have hleftx : (left : ℝ) ≤ z := by simpa [x] using hxz
  let t : unitInterval := ⟨z, left.property.1.trans hleftx,
    (le_of_lt hzy).trans right.property.2⟩
  have hnz0 : 0 ≤ (n : ℝ) * z := mul_nonneg (Nat.cast_nonneg n) t.property.1
  have hfloor : ⌊(n : ℝ) * z⌋₊ = j := by
    by_cases hx : x ≤ (j : ℝ) / n
    · have hz : z = (j : ℝ) / n := max_eq_right hx
      rw [hz]
      have hmul : (n : ℝ) * ((j : ℝ) / n) = j := by
        field_simp [ne_of_gt hnReal]
      rw [hmul, Nat.floor_natCast]
    · have hx' : (j : ℝ) / n < x := lt_of_not_ge hx
      have hjLeft : (j : ℝ) < (n : ℝ) * x :=
        by simpa [mul_comm] using (div_lt_iff₀ hnReal).mp hx'
      have hupper : (n : ℝ) * x < (j : ℝ) + 1 := by
        have hstartCast : (start : ℝ) ≤ j := by exact_mod_cast hstart
        linarith [hleftReal']
      have hz : z = x := max_eq_left (le_of_lt hx')
      rw [hz]
      have hnLeft : 0 ≤ (n : ℝ) * x := by
        dsimp [x]
        exact mul_nonneg (Nat.cast_nonneg n) left.property.1
      exact (Nat.floor_eq_iff hnLeft).2 ⟨le_of_lt hjLeft, hupper⟩
  refine ⟨t, ?_, ?_, ?_⟩
  · exact_mod_cast hxz
  · exact_mod_cast hzy
  · change ⌊(n : ℝ) * z⌋₊ = j
    exact hfloor

/-- A pathwise M₂ corridor event confines every floor-indexed position in
each selected finite-width cell to the spatially rescaled boundary interval.
The time chosen for an integer position is the larger of the cell's left knot
and its grid time, so the left endpoint uses the boundary's right trace. -/
theorem normalizedStepCorridor_subset_selectedHalfOpenCellPositions
    {n : ℕ} {scale : ℕ → ℝ} (hn : 0 < n) (hscale : 0 < scale n)
    (upper lower : StepBoundary)
    (s : Finset (Fin ((StepBoundary.commonKnots upper lower).card - 1)))
    (lo hi : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hlower : ∀ i ∈ s,
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) =
        (lo i : EReal))
    (hupper : ∀ i ∈ s,
      upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) =
        (hi i : EReal)) :
    {increment : ℕ → ℝ |
      RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.PathClass.StepCorridor.corridorSet upper lower} ⊆
      {increment : ℕ → ℝ |
        ∀ i ∈ s, ∀ k < commonPartitionCellStepLength n upper lower i,
          scale n * lo i < AdditivePath.displacement
            (Combinatorics.Sequence.blockStart
              (commonPartitionCellStepLengths n upper lower) i.val + k) increment ∧
          AdditivePath.displacement
              (Combinatorics.Sequence.blockStart
                (commonPartitionCellStepLengths n upper lower) i.val + k) increment <
            scale n * hi i} := by
  intro increment hmem i hiMem k hk
  let left := StepBoundary.commonPartitionGrid upper lower i.val
  let right := StepBoundary.commonPartitionGrid upper lower (i.val + 1)
  let start := commonPartitionFloorTimeIndex n left
  let stop := commonPartitionFloorTimeIndex n right
  let lengths := commonPartitionCellStepLengths n upper lower
  have hstart : Combinatorics.Sequence.blockStart lengths i.val = start := by
    simpa [left, lengths] using blockStart_commonPartitionCellStepLengths n upper lower i
  have hlength : commonPartitionCellStepLength n upper lower i = stop - start := by
    simp [commonPartitionCellStepLength, left, right, start, stop]
  have hgrid : left < right := by
    exact StepBoundary.commonPartitionGrid_strictSucc upper lower i.val i.isLt
  have hfloorMono : start ≤ stop := by
    dsimp [start, stop, left, right]
    exact commonPartitionFloorTimeIndex_mono n (le_of_lt hgrid)
  have hk' : k < stop - start := by simpa [hlength] using hk
  let position := start + k
  have hposition : position < stop := by dsimp [position]; omega
  obtain ⟨t, htleft, htright, htfloor⟩ :=
    exists_commonPartitionCellTime_floor_eq hn
      (left := left) (right := right) (hleft := rfl) (hright := rfl)
      hgrid (Nat.le_add_right start k) hposition
  have hpath :
      RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.PathClass.StepCorridor.corridorSet upper lower := hmem
  change (RandomWalk.normalizedStepCadlagPathIcc scale n increment ⊥ = 0 ∧
    ∀ t : unitInterval,
      lower.eval t <
          (RandomWalk.normalizedStepCadlagPathIcc scale n increment t : EReal) ∧
        (RandomWalk.normalizedStepCadlagPathIcc scale n increment t : EReal) <
          upper.eval t) at hpath
  obtain ⟨_, hcorridor⟩ := hpath
  have hlowerEval := StepBoundary.eval_eq_rightTrace_on_commonPartitionCell_of_le
    lower upper lower
    (fun q hq => StepBoundary.mem_commonKnots_of_mem_lower upper lower hq)
    i (by simpa [left] using htleft) (by simpa [right] using htright)
  have hupperEval := StepBoundary.eval_eq_rightTrace_on_commonPartitionCell_of_le
    upper upper lower
    (fun q hq => StepBoundary.mem_commonKnots_of_mem_upper upper lower hq)
    i (by simpa [left] using htleft) (by simpa [right] using htright)
  have hcorr := hcorridor t
  rw [hlowerEval, hlower i hiMem, hupperEval, hupper i hiMem] at hcorr
  have hpathValue :
      RandomWalk.normalizedStepCadlagPathIcc scale n increment t =
        (scale n)⁻¹ * AdditivePath.displacement position increment := by
    change (scale n)⁻¹ * AdditivePath.displacement
        (⌊(n : ℝ) * (t : ℝ)⌋₊) increment = _
    rw [show ⌊(n : ℝ) * (t : ℝ)⌋₊ = position by
      simpa [commonPartitionFloorTimeIndex, position] using htfloor]
  have hlow : lo i <
      (scale n)⁻¹ * AdditivePath.displacement position increment := by
    have hlowPath : lo i <
        RandomWalk.normalizedStepCadlagPathIcc scale n increment t :=
      EReal.coe_lt_coe_iff.mp hcorr.1
    rw [hpathValue] at hlowPath
    exact hlowPath
  have hhigh : (scale n)⁻¹ * AdditivePath.displacement position increment < hi i := by
    have hhighPath :
        RandomWalk.normalizedStepCadlagPathIcc scale n increment t < hi i :=
      EReal.coe_lt_coe_iff.mp hcorr.2
    rw [hpathValue] at hhighPath
    exact hhighPath
  have hlow' : scale n * lo i < AdditivePath.displacement position increment := by
    calc
      scale n * lo i < scale n *
          ((scale n)⁻¹ * AdditivePath.displacement position increment) :=
        mul_lt_mul_of_pos_left hlow hscale
      _ = AdditivePath.displacement position increment := by
        rw [← mul_assoc, mul_inv_cancel₀ hscale.ne', one_mul]
  have hhigh' : AdditivePath.displacement position increment < scale n * hi i := by
    calc
      AdditivePath.displacement position increment = scale n *
          ((scale n)⁻¹ * AdditivePath.displacement position increment) := by
        rw [← mul_assoc, mul_inv_cancel₀ hscale.ne', one_mul]
      _ < scale n * hi i := mul_lt_mul_of_pos_left hhigh hscale
  rw [hstart]
  simpa [position] using And.intro hlow' hhigh'

/-- Under the IID increment law, a finite step-corridor event is bounded by
the product of the one-cell range probabilities at its floor-rounded common
partition. Only finite-width cells need to be selected. -/
theorem iidSequenceLaw_normalizedStepCorridor_le_selectedCellRangeProduct
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {n : ℕ} {scale : ℕ → ℝ} (hn : 0 < n) (hscale : 0 < scale n)
    (upper lower : StepBoundary)
    (s : Finset (Fin ((StepBoundary.commonKnots upper lower).card - 1)))
    (lo hi : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hlower : ∀ i ∈ s,
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) =
        (lo i : EReal))
    (hupper : ∀ i ∈ s,
      upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) =
        (hi i : EReal))
    (hlength : ∀ i ∈ s, 0 < commonPartitionCellStepLength n upper lower i) :
    iidSequenceLaw ν {increment : ℕ → ℝ |
      RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.PathClass.StepCorridor.corridorSet upper lower} ≤
      ∏ i ∈ s,
        partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
          (scale n * (hi i - lo i))
          (commonPartitionCellStepLength n upper lower i - 1) := by
  let lengths := commonPartitionCellStepLengths n upper lower
  have hsubset := normalizedStepCorridor_subset_selectedHalfOpenCellPositions
    hn hscale upper lower s lo hi hlower hupper
  have hlengthEq (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
      commonPartitionCellStepLength n upper lower i = lengths i.val := by
    simp [commonPartitionCellStepLength, commonPartitionCellStepLengths,
      lengths, i.isLt]
  have hsubset' :
      {increment : ℕ → ℝ |
        RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
          Skorokhod.PathClass.StepCorridor.corridorSet upper lower} ⊆
      {increment : ℕ → ℝ |
        ∀ i ∈ s, ∀ k < lengths i.val,
          scale n * lo i < AdditivePath.displacement
            (Combinatorics.Sequence.blockStart lengths i.val + k) increment ∧
          AdditivePath.displacement
              (Combinatorics.Sequence.blockStart lengths i.val + k) increment <
            scale n * hi i} := by
    intro increment hmem i hiMem k hk
    have hk' : k < commonPartitionCellStepLength n upper lower i := by
      rwa [hlengthEq]
    have hposition := hsubset hmem i hiMem k hk'
    simpa [lengths, hlengthEq i] using hposition
  have hbound :=
    ProbabilityTheory.RandomWalk.measure_forall_selectedHalfOpenPartitionCellCorridors_le_prod_rangeProbability
      ν ((StepBoundary.commonKnots upper lower).card - 1) lengths s
      (fun i => scale n * lo i) (fun i => scale n * hi i)
      (by
        intro i hiMem
        rw [← hlengthEq i]
        exact hlength i hiMem)
  calc
    iidSequenceLaw ν {increment : ℕ → ℝ |
        RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
          Skorokhod.PathClass.StepCorridor.corridorSet upper lower} ≤
      iidSequenceLaw ν {increment : ℕ → ℝ |
        ∀ i ∈ s, ∀ k < lengths i.val,
          scale n * lo i < AdditivePath.displacement
            (Combinatorics.Sequence.blockStart lengths i.val + k) increment ∧
          AdditivePath.displacement
              (Combinatorics.Sequence.blockStart lengths i.val + k) increment <
            scale n * hi i} := measure_mono hsubset'
    _ ≤ ∏ i ∈ s,
          partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
            ((scale n * hi i) - (scale n * lo i)) (lengths i.val - 1) := hbound
    _ = ∏ i ∈ s,
          partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
            (scale n * (hi i - lo i))
            (commonPartitionCellStepLength n upper lower i - 1) := by
      apply Finset.prod_congr rfl
      intro i hiMem
      rw [show (scale n * hi i) - (scale n * lo i) =
          scale n * (hi i - lo i) by ring, ← hlengthEq i]

end ProbabilityTheory.RandomWalk.Path.Block.Partition.StepCorridor

end

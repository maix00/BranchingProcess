/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.PartitionCorridor
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.SourcePath

/-!
# Floor partitions for the source terminal-left convention

The source convention records the positions `S₀, …, S_(n-1)`.  Its finite
partition therefore uses the usual floor indices at every knot below `1`,
and uses `n - 1` at the terminal knot.  This file records that indexing and
the corresponding variable cell lengths.
-/

@[expose] public section

open Filter

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

open ProbabilityTheory.Process.SmallDeviation.Mogulskii

/-- The integer position assigned to a source-convention partition knot.
Clipping the usual floor index at `n - 1` changes only the terminal knot. -/
noncomputable def sourcePartitionKnotIndex (n : ℕ) (upper lower : StepBoundary)
    (j : ℕ) : ℕ :=
  min (commonPartitionFloorTimeIndex n
    (StepBoundary.commonPartitionGrid upper lower j)) (n - 1)

/-- Source-convention cell lengths, extended by zero beyond the finite
partition. Their cumulative sums end at `n - 1`. -/
noncomputable def sourcePartitionCellStepLengths (n : ℕ) (upper lower : StepBoundary) :
    ℕ → ℕ := fun j =>
  if _hj : j < (StepBoundary.commonKnots upper lower).card - 1 then
    sourcePartitionKnotIndex n upper lower (j + 1) -
      sourcePartitionKnotIndex n upper lower j
  else 0

theorem sourcePartitionKnotIndex_mono (n : ℕ) (upper lower : StepBoundary)
    {i j : ℕ} (hij : i ≤ j) :
    sourcePartitionKnotIndex n upper lower i ≤
      sourcePartitionKnotIndex n upper lower j := by
  exact min_le_min
    (commonPartitionFloorTimeIndex_mono n
      (StepBoundary.monotone_commonPartitionGrid upper lower hij)) le_rfl

theorem sourcePartitionKnotIndex_zero (n : ℕ) (upper lower : StepBoundary) :
    sourcePartitionKnotIndex n upper lower 0 = 0 := by
  simp [sourcePartitionKnotIndex, commonPartitionFloorTimeIndex,
    StepBoundary.commonPartitionGrid_zero]

theorem sourcePartitionKnotIndex_last (n : ℕ) (upper lower : StepBoundary) :
    sourcePartitionKnotIndex n upper lower
      ((StepBoundary.commonKnots upper lower).card - 1) = n - 1 := by
  simp [sourcePartitionKnotIndex, commonPartitionFloorTimeIndex,
    StepBoundary.commonPartitionGrid_last]

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

theorem sourcePartitionKnotIndex_eq_floor_of_lt_last
    (n : ℕ) (upper lower : StepBoundary)
    {j : ℕ} (hj : j < (StepBoundary.commonKnots upper lower).card - 1) :
    sourcePartitionKnotIndex n upper lower j =
      commonPartitionFloorTimeIndex n
        (StepBoundary.commonPartitionGrid upper lower j) := by
  apply Nat.min_eq_left
  apply commonPartitionFloorTimeIndex_le_n_sub_one_of_lt_top
  have hgrid : StepBoundary.commonPartitionGrid upper lower j < ⊤ := by
    have hstrict := StepBoundary.commonPartitionGrid_strictSucc upper lower j hj
    have hnext : j + 1 ≤ (StepBoundary.commonKnots upper lower).card - 1 := by
      have hlt := hj
      have hcard : 1 ≤ (StepBoundary.commonKnots upper lower).card := by
        exact Nat.succ_le_iff.mpr
          (Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower))
      omega
    have htail := StepBoundary.monotone_commonPartitionGrid upper lower hnext
    rw [StepBoundary.commonPartitionGrid_last] at htail
    exact lt_of_lt_of_le hstrict htail
  exact hgrid

/-- At each source-partition knot, the terminal-left path records the
position indexed by `sourcePartitionKnotIndex`; at the top this is `S_(n-1)`. -/
theorem sourceNormalizedStepCadlagPathIcc_commonPartitionGrid_apply
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (increment : ℕ → ℝ)
    (upper lower : StepBoundary)
    (j : Fin (StepBoundary.commonKnots upper lower).card) :
    sourceNormalizedStepCadlagPathIcc scale n increment
        (StepBoundary.commonPartitionGrid upper lower j.val) =
      (scale n)⁻¹ * AdditivePath.displacement
        (sourcePartitionKnotIndex n upper lower j.val) increment := by
  by_cases hj : j.val < (StepBoundary.commonKnots upper lower).card - 1
  · have htop : StepBoundary.commonPartitionGrid upper lower j.val ≠ ⊤ := by
      apply ne_of_lt
      have hstrict := StepBoundary.commonPartitionGrid_strictSucc upper lower j.val hj
      have hnext : j.val + 1 ≤ (StepBoundary.commonKnots upper lower).card - 1 := by
        have hcard : 1 ≤ (StepBoundary.commonKnots upper lower).card := by
          exact Nat.succ_le_iff.mpr
            (Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower))
        omega
      have htail := StepBoundary.monotone_commonPartitionGrid upper lower hnext
      rw [StepBoundary.commonPartitionGrid_last] at htail
      exact lt_of_lt_of_le hstrict htail
    rw [sourceNormalizedStepCadlagPathIcc_apply_of_ne_top scale n increment htop,
      sourcePartitionKnotIndex_eq_floor_of_lt_last n upper lower hj]
    change RandomWalk.normalizedStepPath scale n increment
        (StepBoundary.commonPartitionGrid upper lower j.val : ℝ) = _
    rfl
  · have hjlast : j.val = (StepBoundary.commonKnots upper lower).card - 1 := by omega
    have htop : StepBoundary.commonPartitionGrid upper lower j.val = ⊤ := by
      rw [hjlast, StepBoundary.commonPartitionGrid_last]
    rw [htop, sourceNormalizedStepCadlagPathIcc_apply_top scale hn increment,
      hjlast, sourcePartitionKnotIndex_last]

theorem sourcePartitionCellStepLengths_eq_floorDifference
    (n : ℕ) (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    sourcePartitionCellStepLengths n upper lower i.val =
      sourcePartitionKnotIndex n upper lower (i.val + 1) -
        sourcePartitionKnotIndex n upper lower i.val := by
  simp [sourcePartitionCellStepLengths, i.isLt]

theorem blockStart_sourcePartitionCellStepLengths
    (n : ℕ) (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    AdditivePath.blockStart (sourcePartitionCellStepLengths n upper lower) i.val =
      sourcePartitionKnotIndex n upper lower i.val := by
  have hprefix (j : ℕ) (hj : j ≤
      (StepBoundary.commonKnots upper lower).card - 1) :
      AdditivePath.blockStart (sourcePartitionCellStepLengths n upper lower) j =
        sourcePartitionKnotIndex n upper lower j := by
    induction j with
    | zero =>
        simp [sourcePartitionCellStepLengths, sourcePartitionKnotIndex_zero]
    | succ j ih =>
        have hjlt : j < (StepBoundary.commonKnots upper lower).card - 1 := by omega
        rw [AdditivePath.blockStart_succ, ih (by omega)]
        rw [sourcePartitionCellStepLengths, dif_pos hjlt]
        simpa [Nat.succ_eq_add_one] using
          (Nat.add_sub_of_le
            (sourcePartitionKnotIndex_mono n upper lower (Nat.le_succ j)))
  exact hprefix i.val (Nat.le_of_lt i.isLt)

theorem sourcePartitionCellStepLength_eq_common_of_not_last
    (n : ℕ) (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    (hi : i.val + 1 < (StepBoundary.commonKnots upper lower).card - 1) :
    sourcePartitionCellStepLengths n upper lower i.val =
      commonPartitionCellStepLength n upper lower i := by
  rw [sourcePartitionCellStepLengths_eq_floorDifference]
  rw [sourcePartitionKnotIndex_eq_floor_of_lt_last n upper lower hi,
    sourcePartitionKnotIndex_eq_floor_of_lt_last n upper lower (by omega)]
  rfl

theorem sourcePartitionCellStepLength_eq_common_sub_one_last
    (n : ℕ) (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    (hi : i.val + 1 = (StepBoundary.commonKnots upper lower).card - 1) :
    sourcePartitionCellStepLengths n upper lower i.val =
      commonPartitionCellStepLength n upper lower i - 1 := by
  rw [sourcePartitionCellStepLengths_eq_floorDifference,
    show i.val + 1 = (StepBoundary.commonKnots upper lower).card - 1 from hi,
    sourcePartitionKnotIndex_last]
  have hleft := sourcePartitionKnotIndex_eq_floor_of_lt_last n upper lower i.isLt
  rw [hleft]
  have htop : commonPartitionFloorTimeIndex n ⊤ = n := by
    simp [commonPartitionFloorTimeIndex]
  have hcommon : commonPartitionCellStepLength n upper lower i =
      n - commonPartitionFloorTimeIndex n
        (StepBoundary.commonPartitionGrid upper lower i.val) := by
    unfold commonPartitionCellStepLength
    rw [show i.val + 1 = (StepBoundary.commonKnots upper lower).card - 1 by omega,
      StepBoundary.commonPartitionGrid_last, htop]
  rw [hcommon]
  have hleftle := commonPartitionFloorTimeIndex_le_n_sub_one_of_lt_top n
    (by
      have hleftlt : StepBoundary.commonPartitionGrid upper lower i.val < ⊤ := by
        have hstrict := StepBoundary.commonPartitionGrid_strictSucc upper lower i.val i.isLt
        rw [hi, StepBoundary.commonPartitionGrid_last] at hstrict
        exact hstrict
      exact hleftlt)
  omega

theorem tendsto_sourcePartitionCellStepLength_div_nat
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    Tendsto
      (fun n => (sourcePartitionCellStepLengths n upper lower i.val : ℝ) /
        (n : ℝ)) atTop
      (nhds ((StepBoundary.commonPartitionGrid upper lower (i.val + 1) : unitInterval) -
        StepBoundary.commonPartitionGrid upper lower i.val)) := by
  have hlastOrNot : i.val + 1 = (StepBoundary.commonKnots upper lower).card - 1 ∨
      i.val + 1 < (StepBoundary.commonKnots upper lower).card - 1 := by omega
  rcases hlastOrNot with hlast | hnotlast
  · have heq : (fun n =>
        (sourcePartitionCellStepLengths n upper lower i.val : ℝ) / (n : ℝ)) =ᶠ[atTop]
        fun n =>
          ((commonPartitionCellStepLength n upper lower i - 1 : ℕ) : ℝ) /
            (n : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      rw [sourcePartitionCellStepLength_eq_common_sub_one_last n upper lower i hlast]
    exact (tendsto_commonPartitionCellRangeHorizon_div_nat upper lower i).congr' heq.symm
  · have heq : (fun n =>
        (sourcePartitionCellStepLengths n upper lower i.val : ℝ) / (n : ℝ)) =
        fun n => (commonPartitionCellStepLength n upper lower i : ℝ) / (n : ℝ) := by
      funext n
      exact congrArg (fun k : ℕ => (k : ℝ) / (n : ℝ))
        (sourcePartitionCellStepLength_eq_common_of_not_last n upper lower i hnotlast)
    have heq' : (fun n => (commonPartitionCellStepLength n upper lower i : ℝ) / (n : ℝ)) =ᶠ[atTop]
        fun n => (sourcePartitionCellStepLengths n upper lower i.val : ℝ) / (n : ℝ) :=
      Filter.Eventually.of_forall fun n => (congrFun heq n).symm
    exact (tendsto_commonPartitionCellStepLength_div_nat upper lower i).congr' heq'

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

end

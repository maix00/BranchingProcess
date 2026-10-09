/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.SourcePartition
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.PartitionRange

/-!
# Cell estimates for the source terminal-left path

The terminal-left convention has the same observed half-open cell positions
as the right-continuous path: the final such position is `S_(n-1)`. Therefore
the existing variable-block independence bound and its `cellLength - 1`
range horizon apply without an additive probability error.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.Process.SmallDeviation.Mogulskii

private theorem stepBoundary_eval_eq_rightTrace_of_mem_sourceCell
    (b upper lower : StepBoundary)
    (hknots : ∀ q ∈ b.knots, q ∈ StepBoundary.commonKnots upper lower)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    {t : unitInterval}
    (hleft : StepBoundary.commonPartitionGrid upper lower i.val ≤ t)
    (hright : t < StepBoundary.commonPartitionGrid upper lower (i.val + 1)) :
    b.eval t = b.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) := by
  by_cases hteq : t = StepBoundary.commonPartitionGrid upper lower i.val
  · subst t
    exact (StepBoundary.rightTrace_eq_eval b _).symm
  · exact StepBoundary.eval_eq_rightTrace_on_commonPartitionCell
      b upper lower hknots i.val i.isLt
      (lt_of_le_of_ne hleft (Ne.symm hteq)) hright

/-- A source-convention strict corridor confines every position in the
half-open floor cells, including the final position `S_(n-1)`. -/
theorem sourceNormalizedStepCorridor_subset_selectedHalfOpenCellPositions
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
      sourceNormalizedStepCadlagPathIcc scale n increment ∈
        ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet upper lower} ⊆
      {increment : ℕ → ℝ |
        ∀ i ∈ s, ∀ k < commonPartitionCellStepLength n upper lower i,
          scale n * lo i < AdditivePath.displacement
            (AdditivePath.blockStart
              (commonPartitionCellStepLengths n upper lower) i.val + k) increment ∧
          AdditivePath.displacement
              (AdditivePath.blockStart
                (commonPartitionCellStepLengths n upper lower) i.val + k) increment <
            scale n * hi i} := by
  intro increment hmem i hiMem k hk
  let left := StepBoundary.commonPartitionGrid upper lower i.val
  let right := StepBoundary.commonPartitionGrid upper lower (i.val + 1)
  let start := commonPartitionFloorTimeIndex n left
  let stop := commonPartitionFloorTimeIndex n right
  let lengths := commonPartitionCellStepLengths n upper lower
  have hstart : AdditivePath.blockStart lengths i.val = start := by
    simpa [left, lengths] using blockStart_commonPartitionCellStepLengths n upper lower i
  have hlength : commonPartitionCellStepLength n upper lower i = stop - start := by
    simp [commonPartitionCellStepLength, left, right, start, stop]
  have hgrid : left < right :=
    StepBoundary.commonPartitionGrid_strictSucc upper lower i.val i.isLt
  have hfloorMono : start ≤ stop := by
    dsimp [start, stop, left, right]
    exact commonPartitionFloorTimeIndex_mono n hgrid.le
  have hk' : k < stop - start := by simpa [hlength] using hk
  let position := start + k
  have hposition : position < stop := by dsimp [position]; omega
  obtain ⟨t, htleft, htright, htfloor⟩ :=
    exists_commonPartitionCellTime_floor_eq hn
      (left := left) (right := right) (hleft := rfl) (hright := rfl)
      hgrid (Nat.le_add_right start k) hposition
  have hcorridorSet := hmem
  change sourceNormalizedStepCadlagPathIcc scale n increment ⊥ = 0 ∧
    ∀ t : unitInterval,
      lower.eval t < (sourceNormalizedStepCadlagPathIcc scale n increment t : EReal) ∧
        (sourceNormalizedStepCadlagPathIcc scale n increment t : EReal) < upper.eval t
    at hcorridorSet
  obtain ⟨_, hcorridor⟩ := hcorridorSet
  have hlowerEval := stepBoundary_eval_eq_rightTrace_of_mem_sourceCell
    lower upper lower
    (fun q hq => StepBoundary.mem_commonKnots_of_mem_lower upper lower hq)
    i (by simpa [left] using htleft) (by simpa [right] using htright)
  have hupperEval := stepBoundary_eval_eq_rightTrace_of_mem_sourceCell
    upper upper lower
    (fun q hq => StepBoundary.mem_commonKnots_of_mem_upper upper lower hq)
    i (by simpa [left] using htleft) (by simpa [right] using htright)
  have hcorr := hcorridor t
  rw [hlowerEval, hlower i hiMem, hupperEval, hupper i hiMem] at hcorr
  have htne : t ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_lt_of_le htright right.property.2
  have hpathValue :
      sourceNormalizedStepCadlagPathIcc scale n increment t =
        (scale n)⁻¹ * AdditivePath.displacement position increment := by
    rw [sourceNormalizedStepCadlagPathIcc_apply_of_ne_top scale n increment htne]
    change (scale n)⁻¹ * AdditivePath.displacement
        (⌊(n : ℝ) * (t : ℝ)⌋₊) increment = _
    rw [show ⌊(n : ℝ) * (t : ℝ)⌋₊ = position by
      simpa [commonPartitionFloorTimeIndex, position] using htfloor]
  have hlow : lo i <
      (scale n)⁻¹ * AdditivePath.displacement position increment := by
    have hlowPath : lo i < sourceNormalizedStepCadlagPathIcc scale n increment t :=
      EReal.coe_lt_coe_iff.mp hcorr.1
    rw [hpathValue] at hlowPath
    exact hlowPath
  have hhigh : (scale n)⁻¹ * AdditivePath.displacement position increment < hi i := by
    have hhighPath :
        sourceNormalizedStepCadlagPathIcc scale n increment t < hi i :=
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

/-- The source-convention finite-partition corridor probability has the same
selected-cell range-product upper bound. The final range horizon is exactly
`n - 1 - floor(n * t_{m-1})`. -/
theorem iidSequenceLaw_sourceNormalizedStepCorridor_le_selectedCellRangeProduct
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
      sourceNormalizedStepCadlagPathIcc scale n increment ∈
        ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet upper lower} ≤
      ∏ i ∈ s,
        partialSumRangeOscillationLTProbability (iidSequenceLaw ν)
          (scale n * (hi i - lo i))
          (commonPartitionCellStepLength n upper lower i - 1) := by
  let lengths := commonPartitionCellStepLengths n upper lower
  have hsubset := sourceNormalizedStepCorridor_subset_selectedHalfOpenCellPositions
    hn hscale upper lower s lo hi hlower hupper
  have hlengthEq (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
      commonPartitionCellStepLength n upper lower i = lengths i.val := by
    simp [commonPartitionCellStepLength, commonPartitionCellStepLengths, lengths, i.isLt]
  have hsubset' :
      {increment : ℕ → ℝ |
        sourceNormalizedStepCadlagPathIcc scale n increment ∈
          ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet upper lower} ⊆
      {increment : ℕ → ℝ |
        ∀ i ∈ s, ∀ k < lengths i.val,
          scale n * lo i < AdditivePath.displacement
            (AdditivePath.blockStart lengths i.val + k) increment ∧
          AdditivePath.displacement
              (AdditivePath.blockStart lengths i.val + k) increment < scale n * hi i} := by
    intro increment hmem i hiMem k hk
    have hk' : k < commonPartitionCellStepLength n upper lower i := by
      rwa [hlengthEq]
    have hposition := hsubset hmem i hiMem k hk'
    simpa [lengths, hlengthEq i] using hposition
  have hbound :=
    ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.measure_forall_selectedHalfOpenPartitionCellCorridors_le_prod_rangeProbability
      ν ((StepBoundary.commonKnots upper lower).card - 1) lengths s
      (fun i => scale n * lo i) (fun i => scale n * hi i)
      (by
        intro i hiMem
        rw [← hlengthEq i]
        exact hlength i hiMem)
  calc
    iidSequenceLaw ν {increment : ℕ → ℝ |
        sourceNormalizedStepCadlagPathIcc scale n increment ∈
          ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet upper lower} ≤
      iidSequenceLaw ν {increment : ℕ → ℝ |
        ∀ i ∈ s, ∀ k < lengths i.val,
          scale n * lo i < AdditivePath.displacement
            (AdditivePath.blockStart lengths i.val + k) increment ∧
          AdditivePath.displacement
              (AdditivePath.blockStart lengths i.val + k) increment < scale n * hi i} :=
      measure_mono hsubset'
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

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

end

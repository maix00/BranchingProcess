/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.PartitionLowerGeometry

/-!
# Finite-partition lower probability bound

The deterministic lower gluing and independence of adjacent IID blocks give
a product lower bound for the full discrete corridor probability.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.Process.SmallDeviation.Mogulskii

/-- The product of the local endpoint-core probabilities is a lower bound
for the full floor-partitioned strict corridor probability. Each factor is
the one-cell event under the original IID increment law; the bridge event
uses the source's incoming-core contraction and outgoing endpoint band. -/
theorem iidSequenceLaw_normalizedStepCorridor_ge_prod_partitionCellCoreReturnProbability
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {n : ℕ} {scale : ℕ → ℝ} (hscale : 0 < scale n)
    (upper lower : StepBoundary)
    (center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ)
    (innerLower innerUpper :
      Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hcenter0 : ∀ j, j.val = 0 → center j = 0)
    (hradius0 : ∀ j, j.val = 0 → radius j = 0)
    (hradiusStep : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      radius (commonPartitionCellLeftKnotIndex upper lower i) <
        radius (commonPartitionCellRightKnotIndex upper lower i))
    (hcores : ∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      center j - radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val) ∧
      center j + radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val))
    (hgeometry : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) <
          (innerLower i : EReal) ∧
        (innerUpper i : EReal) <
          upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)) :
    (∏ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0
            (commonPartitionCellStepLengths n upper lower i.val) increment ∈
          {block | partitionCellCoreReturnBlockEvent
            (scale n * innerLower i) (scale n * innerUpper i)
            (scale n * center (commonPartitionCellLeftKnotIndex upper lower i))
            (scale n * radius (commonPartitionCellLeftKnotIndex upper lower i))
            (scale n * center (commonPartitionCellRightKnotIndex upper lower i))
            (scale n * radius (commonPartitionCellRightKnotIndex upper lower i)) block}}) ≤
      iidSequenceLaw ν {increment : ℕ → ℝ |
        RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
          ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet upper lower} := by
  let lengths := commonPartitionCellStepLengths n upper lower
  let blockEvent : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      Set (Fin (lengths i.val) → ℝ) := fun i =>
    {block | partitionCellCoreReturnBlockEvent
      (scale n * innerLower i) (scale n * innerUpper i)
      (scale n * center (commonPartitionCellLeftKnotIndex upper lower i))
      (scale n * radius (commonPartitionCellLeftKnotIndex upper lower i))
      (scale n * center (commonPartitionCellRightKnotIndex upper lower i))
      (scale n * radius (commonPartitionCellRightKnotIndex upper lower i)) block}
  have hsubset :
      {increment : ℕ → ℝ | ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        Combinatorics.Sequence.blockCoordinates
            (AdditivePath.blockStart lengths i.val) (lengths i.val) increment ∈
          blockEvent i} ⊆
      {increment : ℕ → ℝ |
        RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
          ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet upper lower} := by
    intro increment hevents
    exact normalizedStepCadlagPathIcc_mem_corridorSet_of_partitionCellCoreReturnBlockEvents
      hscale upper lower center radius innerLower innerUpper hcenter0 hradius0
      (by simpa [commonPartitionCellLeftKnotIndex, commonPartitionCellRightKnotIndex]
        using hradiusStep) hcores hgeometry (by
          intro i
          simpa [lengths, blockEvent,
            commonPartitionCellLeftKnotIndex, commonPartitionCellRightKnotIndex] using
            hevents i)
  have hfactor := iidSequenceLaw_forall_partitionCellCoreReturnBlockEvent_eq_prod
    ν lengths ((StepBoundary.commonKnots upper lower).card - 1)
    (fun i => scale n * innerLower i)
    (fun i => scale n * innerUpper i)
    (fun i => scale n * center (commonPartitionCellLeftKnotIndex upper lower i))
    (fun i => scale n * radius (commonPartitionCellLeftKnotIndex upper lower i))
    (fun i => scale n * center (commonPartitionCellRightKnotIndex upper lower i))
    (fun i => scale n * radius (commonPartitionCellRightKnotIndex upper lower i))
  calc
    (∏ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0
            (commonPartitionCellStepLengths n upper lower i.val) increment ∈
          {block | partitionCellCoreReturnBlockEvent
            (scale n * innerLower i) (scale n * innerUpper i)
            (scale n * center (commonPartitionCellLeftKnotIndex upper lower i))
            (scale n * radius (commonPartitionCellLeftKnotIndex upper lower i))
            (scale n * center (commonPartitionCellRightKnotIndex upper lower i))
            (scale n * radius (commonPartitionCellRightKnotIndex upper lower i)) block}}) =
        iidSequenceLaw ν {increment : ℕ → ℝ | ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
          Combinatorics.Sequence.blockCoordinates
              (AdditivePath.blockStart lengths i.val) (lengths i.val) increment ∈
            blockEvent i} := by
      simpa [lengths, blockEvent] using hfactor.symm
    _ ≤ iidSequenceLaw ν {increment : ℕ → ℝ |
          RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
            ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet upper lower} :=
      measure_mono hsubset

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

end

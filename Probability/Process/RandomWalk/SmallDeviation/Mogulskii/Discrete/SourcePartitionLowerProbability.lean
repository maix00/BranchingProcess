/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.SourcePartitionLowerGeometry
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.PartitionLowerProbability

/-! # Lower probability bounds for source-convention corridors -/

@[expose] public section

open Filter MeasureTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

open ProbabilityTheory.RandomWalk
open Skorokhod.PathClass.StepCorridor
open Skorokhod.PathClass.StepCorridor

theorem iidSequenceLaw_sourceNormalizedStepCorridor_ge_prod_partitionCellCoreReturnProbability
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {n : ℕ} {scale : ℕ → ℝ} (hn : 0 < n) (hscale : 0 < scale n)
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
            (sourcePartitionCellStepLengths n upper lower i.val) increment ∈
          {block | partitionCellCoreReturnBlockEvent
            (scale n * innerLower i) (scale n * innerUpper i)
            (scale n * center (commonPartitionCellLeftKnotIndex upper lower i))
            (scale n * radius (commonPartitionCellLeftKnotIndex upper lower i))
            (scale n * center (commonPartitionCellRightKnotIndex upper lower i))
            (scale n * radius (commonPartitionCellRightKnotIndex upper lower i)) block}}) ≤
      iidSequenceLaw ν {increment : ℕ → ℝ |
        sourceNormalizedStepCadlagPathIcc scale n increment ∈
          Skorokhod.PathClass.StepCorridor.corridorSet upper lower} := by
  let lengths := sourcePartitionCellStepLengths n upper lower
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
        sourceNormalizedStepCadlagPathIcc scale n increment ∈
          Skorokhod.PathClass.StepCorridor.corridorSet upper lower} := by
    intro increment hevents
    exact sourceNormalizedStepCadlagPathIcc_mem_corridorSet_of_partitionCellCoreReturnBlockEvents
      hn hscale upper lower center radius innerLower innerUpper hcenter0 hradius0
      (by simpa [commonPartitionCellLeftKnotIndex, commonPartitionCellRightKnotIndex]
        using hradiusStep) hcores hgeometry (by
          intro i
          simpa [lengths, blockEvent,
            commonPartitionCellLeftKnotIndex, commonPartitionCellRightKnotIndex] using
            hevents i)
  have hprod := iidSequenceLaw_partitionCellCoreReturnBlocks_ge_of_subset ν lengths
    ((StepBoundary.commonKnots upper lower).card - 1)
    (fun i => scale n * innerLower i)
    (fun i => scale n * innerUpper i)
    (fun i => scale n * center (commonPartitionCellLeftKnotIndex upper lower i))
    (fun i => scale n * radius (commonPartitionCellLeftKnotIndex upper lower i))
    (fun i => scale n * center (commonPartitionCellRightKnotIndex upper lower i))
    (fun i => scale n * radius (commonPartitionCellRightKnotIndex upper lower i))
    {increment : ℕ → ℝ |
      sourceNormalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.PathClass.StepCorridor.corridorSet upper lower}
    hsubset
  simpa [lengths, blockEvent] using hprod

/-- Any eventual lower bounds for the independent local core-return events
multiply to a lower bound for the full strict corridor probability. Keeping
the local bounds abstract lets the stable bridge argument supply each cell's
own width, amplitude, and block count. -/
theorem eventually_iidSequenceLaw_sourceNormalizedStepCorridor_ge_prod_of_partitionCellCoreReturnBounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {scale : ℕ → ℝ}
    (hscale : ∀ᶠ n : ℕ in atTop, 0 < scale n)
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
          upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val))
    (localLower : Fin ((StepBoundary.commonKnots upper lower).card - 1) →
      ℕ → ENNReal)
    (hlocal : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      ∀ᶠ n : ℕ in atTop,
        localLower i n ≤ iidSequenceLaw ν
          {increment : ℕ → ℝ |
            Combinatorics.Sequence.blockCoordinates 0
                (sourcePartitionCellStepLengths n upper lower i.val) increment ∈
              {block | partitionCellCoreReturnBlockEvent
                (scale n * innerLower i) (scale n * innerUpper i)
                (scale n * center (commonPartitionCellLeftKnotIndex upper lower i))
                (scale n * radius (commonPartitionCellLeftKnotIndex upper lower i))
                (scale n * center (commonPartitionCellRightKnotIndex upper lower i))
                (scale n * radius (commonPartitionCellRightKnotIndex upper lower i)) block}}) :
    ∀ᶠ n : ℕ in atTop,
      (∏ i : Fin ((StepBoundary.commonKnots upper lower).card - 1), localLower i n) ≤
        iidSequenceLaw ν {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale n increment ∈
            Skorokhod.PathClass.StepCorridor.corridorSet upper lower} := by
  have hlocalAll : ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        localLower i n ≤ iidSequenceLaw ν
          {increment : ℕ → ℝ |
            Combinatorics.Sequence.blockCoordinates 0
                (sourcePartitionCellStepLengths n upper lower i.val) increment ∈
              {block | partitionCellCoreReturnBlockEvent
                (scale n * innerLower i) (scale n * innerUpper i)
                (scale n * center (commonPartitionCellLeftKnotIndex upper lower i))
                (scale n * radius (commonPartitionCellLeftKnotIndex upper lower i))
                (scale n * center (commonPartitionCellRightKnotIndex upper lower i))
                (scale n * radius (commonPartitionCellRightKnotIndex upper lower i)) block}} := by
    filter_upwards [(Finset.eventually_all Finset.univ).2 fun i _ => hlocal i]
      with n hn
    intro i
    exact hn i (Finset.mem_univ _)
  filter_upwards [hlocalAll, hscale, eventually_gt_atTop (0 : ℕ)]
    with n hlocalN hscaleN hn
  have hfactor := iidSequenceLaw_sourceNormalizedStepCorridor_ge_prod_partitionCellCoreReturnProbability
    ν hn hscaleN upper lower center radius innerLower innerUpper
    hcenter0 hradius0 hradiusStep hcores hgeometry
  calc
    (∏ i : Fin ((StepBoundary.commonKnots upper lower).card - 1), localLower i n) ≤
        ∏ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
          iidSequenceLaw ν
            {increment : ℕ → ℝ |
              Combinatorics.Sequence.blockCoordinates 0
                  (sourcePartitionCellStepLengths n upper lower i.val) increment ∈
                {block | partitionCellCoreReturnBlockEvent
                  (scale n * innerLower i) (scale n * innerUpper i)
                  (scale n * center (commonPartitionCellLeftKnotIndex upper lower i))
                  (scale n * radius (commonPartitionCellLeftKnotIndex upper lower i))
                  (scale n * center (commonPartitionCellRightKnotIndex upper lower i))
                  (scale n * radius (commonPartitionCellRightKnotIndex upper lower i)) block}} := by
      apply Finset.prod_le_prod
      intro i hi
      exact hlocalN i
    _ ≤ iidSequenceLaw ν
        {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale n increment ∈
            Skorokhod.PathClass.StepCorridor.corridorSet upper lower} := by
      simpa using hfactor


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

end

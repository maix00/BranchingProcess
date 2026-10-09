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
open Skorokhod.PathClass.StepCorridor
open Skorokhod.PathClass.StepCorridor

/-- Independent endpoint-core events on any finite family of consecutive
variable-length blocks give their product probability. The explicit `lengths`
sequence lets path-convention adapters choose their own cumulative cell
indices while sharing the same IID factorization proof. -/
theorem iidSequenceLaw_partitionCellCoreReturnBlocks_ge_of_subset
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (lengths : ℕ → ℕ) (blocks : ℕ)
    (innerLower innerUpper startCenter startRadius endCenter endRadius :
      Fin blocks → ℝ)
    (target : Set (ℕ → ℝ))
    (hsubset : {increment : ℕ → ℝ |
      ∀ i : Fin blocks,
        Combinatorics.Sequence.blockCoordinates
          (AdditivePath.blockStart lengths i.val) (lengths i.val) increment ∈
          {block | partitionCellCoreReturnBlockEvent
            (innerLower i) (innerUpper i) (startCenter i) (startRadius i)
            (endCenter i) (endRadius i) block}} ⊆ target) :
    (∏ i : Fin blocks, iidSequenceLaw ν {increment : ℕ → ℝ |
      Combinatorics.Sequence.blockCoordinates 0 (lengths i.val) increment ∈
        {block | partitionCellCoreReturnBlockEvent
          (innerLower i) (innerUpper i) (startCenter i) (startRadius i)
          (endCenter i) (endRadius i) block}}) ≤ iidSequenceLaw ν target := by
  have hfactor := iidSequenceLaw_forall_partitionCellCoreReturnBlockEvent_eq_prod
    ν lengths blocks innerLower innerUpper startCenter startRadius endCenter endRadius
  calc
    (∏ i : Fin blocks, iidSequenceLaw ν {increment : ℕ → ℝ |
      Combinatorics.Sequence.blockCoordinates 0 (lengths i.val) increment ∈
        {block | partitionCellCoreReturnBlockEvent
          (innerLower i) (innerUpper i) (startCenter i) (startRadius i)
          (endCenter i) (endRadius i) block}}) =
        iidSequenceLaw ν {increment : ℕ → ℝ |
          ∀ i : Fin blocks,
            Combinatorics.Sequence.blockCoordinates
              (AdditivePath.blockStart lengths i.val) (lengths i.val) increment ∈
              {block | partitionCellCoreReturnBlockEvent
                (innerLower i) (innerUpper i) (startCenter i) (startRadius i)
                (endCenter i) (endRadius i) block}} := hfactor.symm
    _ ≤ iidSequenceLaw ν target := measure_mono hsubset

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
          Skorokhod.PathClass.StepCorridor.corridorSet upper lower} := by
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
          Skorokhod.PathClass.StepCorridor.corridorSet upper lower} := by
    intro increment hevents
    exact normalizedStepCadlagPathIcc_mem_corridorSet_of_partitionCellCoreReturnBlockEvents
      hscale upper lower center radius innerLower innerUpper hcenter0 hradius0
      (by simpa [commonPartitionCellLeftKnotIndex, commonPartitionCellRightKnotIndex]
        using hradiusStep) hcores hgeometry (by
          intro i
          simpa [lengths, blockEvent,
            commonPartitionCellLeftKnotIndex, commonPartitionCellRightKnotIndex] using
            hevents i)
  apply iidSequenceLaw_partitionCellCoreReturnBlocks_ge_of_subset ν lengths
    ((StepBoundary.commonKnots upper lower).card - 1)
    (fun i => scale n * innerLower i)
    (fun i => scale n * innerUpper i)
    (fun i => scale n * center (commonPartitionCellLeftKnotIndex upper lower i))
    (fun i => scale n * radius (commonPartitionCellLeftKnotIndex upper lower i))
    (fun i => scale n * center (commonPartitionCellRightKnotIndex upper lower i))
    (fun i => scale n * radius (commonPartitionCellRightKnotIndex upper lower i))
    {increment : ℕ → ℝ |
      RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.PathClass.StepCorridor.corridorSet upper lower}
  simpa [lengths, blockEvent] using hsubset

/-- Any eventual lower bounds for the independent local core-return events
multiply to a lower bound for the full strict corridor probability. Keeping
the local bounds abstract lets the stable bridge argument supply each cell's
own width, amplitude, and block count. -/
theorem eventually_iidSequenceLaw_normalizedStepCorridor_ge_prod_of_partitionCellCoreReturnBounds
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
                (commonPartitionCellStepLengths n upper lower i.val) increment ∈
              {block | partitionCellCoreReturnBlockEvent
                (scale n * innerLower i) (scale n * innerUpper i)
                (scale n * center (commonPartitionCellLeftKnotIndex upper lower i))
                (scale n * radius (commonPartitionCellLeftKnotIndex upper lower i))
                (scale n * center (commonPartitionCellRightKnotIndex upper lower i))
                (scale n * radius (commonPartitionCellRightKnotIndex upper lower i)) block}}) :
    ∀ᶠ n : ℕ in atTop,
      (∏ i : Fin ((StepBoundary.commonKnots upper lower).card - 1), localLower i n) ≤
        iidSequenceLaw ν {increment : ℕ → ℝ |
          RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
            Skorokhod.PathClass.StepCorridor.corridorSet upper lower} := by
  have hlocalAll : ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        localLower i n ≤ iidSequenceLaw ν
          {increment : ℕ → ℝ |
            Combinatorics.Sequence.blockCoordinates 0
                (commonPartitionCellStepLengths n upper lower i.val) increment ∈
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
  filter_upwards [hlocalAll, hscale] with n hlocalN hscaleN
  have hfactor := iidSequenceLaw_normalizedStepCorridor_ge_prod_partitionCellCoreReturnProbability
    ν hscaleN upper lower center radius innerLower innerUpper
    hcenter0 hradius0 hradiusStep hcores hgeometry
  calc
    (∏ i : Fin ((StepBoundary.commonKnots upper lower).card - 1), localLower i n) ≤
        ∏ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
          iidSequenceLaw ν
            {increment : ℕ → ℝ |
              Combinatorics.Sequence.blockCoordinates 0
                  (commonPartitionCellStepLengths n upper lower i.val) increment ∈
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
          RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
            Skorokhod.PathClass.StepCorridor.corridorSet upper lower} := by
      simpa using hfactor

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Walk.Path.Block.Partition.Normalized
public import Probability.BranchingRandomWalk.Walk.Path.Block.Corridor

/-!
# Probability bounds for partitioned walk paths

Deterministic finite-partition corridor inclusions are lifted to measure
inequalities. No independence or moment assumptions are imposed here.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- Normalized endpoint containment in shrunken intervals transfers to the
unnormalized margins used by the block-corridor estimate. -/
theorem measure_normalizedEndpoints_le_partitionStartMargins
    (incrementLaw : Measure (ℕ → ℝ))
    {blocks length : ℕ} {scale radius : ℝ} (hscale : 0 < scale)
    (lower upper : ℕ → ℝ) :
    incrementLaw {increment | ∀ j < blocks,
        partialSum (j * length) increment / scale ∈
          Set.Ioo (lower j + radius) (upper j - radius)} ≤
      incrementLaw {increment | ∀ j < blocks,
        scale * lower j + scale * radius ≤
            partialSum (j * length) increment ∧
          partialSum (j * length) increment ≤
            scale * upper j - scale * radius} :=
  measure_mono fun _increment hendpoints =>
    partitionStartMargins_of_normalizedEndpoints hscale hendpoints

/-- Simultaneous block-start margins are bounded by the probability of all
block corridors plus the sum of the individual large-deviation events. -/
theorem measure_partitionStartMargins_le_corridors_add_sum_largeDeviation
    (incrementLaw : Measure (ℕ → ℝ))
    {blocks length : ℕ} {radius : ℝ} (hradius : 0 ≤ radius)
    (lower upper : ℕ → ℝ) :
    incrementLaw {increment | ∀ j < blocks,
        lower j + radius ≤ partialSum (j * length) increment ∧
          partialSum (j * length) increment ≤ upper j - radius} ≤
      incrementLaw {increment | ∀ j < blocks, ∀ k ≤ length,
          partialSum (j * length + k) increment ∈
            Set.Icc (lower j) (upper j)} +
        ∑ j ∈ Finset.range blocks,
          incrementLaw {increment |
            ∃ k ∈ Finset.range (length + 1),
              radius ≤ |blockSum (j * length) (k + 1) increment|} := by
  let margins : Set (ℕ → ℝ) := {increment | ∀ j < blocks,
    lower j + radius ≤ partialSum (j * length) increment ∧
      partialSum (j * length) increment ≤ upper j - radius}
  let corridors : Set (ℕ → ℝ) := {increment | ∀ j < blocks,
    ∀ k ≤ length, partialSum (j * length + k) increment ∈
      Set.Icc (lower j) (upper j)}
  let large (j : ℕ) : Set (ℕ → ℝ) := {increment |
    ∃ k ∈ Finset.range (length + 1),
      radius ≤ |blockSum (j * length) (k + 1) increment|}
  have hsubset : margins ⊆ corridors ∪
      {increment | ∃ j < blocks, increment ∈ large j} :=
    partitionStartMargins_subset_corridors_union_largeDeviation
      hradius lower upper
  have hlarge :
      incrementLaw {increment | ∃ j < blocks, increment ∈ large j} ≤
        ∑ j ∈ Finset.range blocks, incrementLaw (large j) := by
    rw [show {increment | ∃ j < blocks, increment ∈ large j} =
        ⋃ j ∈ Finset.range blocks, large j by
      ext increment
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
      aesop]
    exact measure_biUnion_finset_le _ _
  calc
    incrementLaw margins ≤ incrementLaw (corridors ∪
        {increment | ∃ j < blocks, increment ∈ large j}) :=
      measure_mono hsubset
    _ ≤ incrementLaw corridors +
        incrementLaw {increment | ∃ j < blocks, increment ∈ large j} :=
      measure_union_le _ _
    _ ≤ incrementLaw corridors +
        ∑ j ∈ Finset.range blocks, incrementLaw (large j) :=
      add_le_add_right hlarge _

/-- The same corridor comparison preserves an arbitrary additional endpoint
event.  The exceptional large-oscillation union need not preserve it. -/
theorem measure_partitionStartMargins_inter_le_corridors_inter_add_sum_largeDeviation
    (incrementLaw : Measure (ℕ → ℝ))
    {blocks length : ℕ} {radius : ℝ} (hradius : 0 ≤ radius)
    (lower upper : ℕ → ℝ) (final : Set (ℕ → ℝ)) :
    incrementLaw ({increment | ∀ j < blocks,
        lower j + radius ≤ partialSum (j * length) increment ∧
          partialSum (j * length) increment ≤ upper j - radius} ∩ final) ≤
      incrementLaw ({increment | ∀ j < blocks, ∀ k ≤ length,
          partialSum (j * length + k) increment ∈
            Set.Icc (lower j) (upper j)} ∩ final) +
        ∑ j ∈ Finset.range blocks,
          incrementLaw {increment |
            ∃ k ∈ Finset.range (length + 1),
              radius ≤ |blockSum (j * length) (k + 1) increment|} := by
  let margins : Set (ℕ → ℝ) := {increment | ∀ j < blocks,
    lower j + radius ≤ partialSum (j * length) increment ∧
      partialSum (j * length) increment ≤ upper j - radius}
  let corridors : Set (ℕ → ℝ) := {increment | ∀ j < blocks,
    ∀ k ≤ length, partialSum (j * length + k) increment ∈
      Set.Icc (lower j) (upper j)}
  let large (j : ℕ) : Set (ℕ → ℝ) := {increment |
    ∃ k ∈ Finset.range (length + 1),
      radius ≤ |blockSum (j * length) (k + 1) increment|}
  have hbase : margins ⊆ corridors ∪
      {increment | ∃ j < blocks, increment ∈ large j} :=
    partitionStartMargins_subset_corridors_union_largeDeviation
      hradius lower upper
  have hsubset : margins ∩ final ⊆
      (corridors ∩ final) ∪ {increment | ∃ j < blocks,
        increment ∈ large j} := by
    rintro increment ⟨hmargins, hfinal⟩
    rcases hbase hmargins with hcorridors | hlarge
    · exact Or.inl ⟨hcorridors, hfinal⟩
    · exact Or.inr hlarge
  have hlarge :
      incrementLaw {increment | ∃ j < blocks, increment ∈ large j} ≤
        ∑ j ∈ Finset.range blocks, incrementLaw (large j) := by
    rw [show {increment | ∃ j < blocks, increment ∈ large j} =
        ⋃ j ∈ Finset.range blocks, large j by
      ext increment
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
      aesop]
    exact measure_biUnion_finset_le _ _
  calc
    incrementLaw (margins ∩ final) ≤ incrementLaw
        ((corridors ∩ final) ∪
          {increment | ∃ j < blocks, increment ∈ large j}) :=
      measure_mono hsubset
    _ ≤ incrementLaw (corridors ∩ final) +
        incrementLaw {increment | ∃ j < blocks, increment ∈ large j} :=
      measure_union_le _ _
    _ ≤ incrementLaw (corridors ∩ final) +
        ∑ j ∈ Finset.range blocks, incrementLaw (large j) :=
      add_le_add_right hlarge _

/-- Normalized start-endpoint containment, together with a final endpoint
event, transfers to full block corridors while retaining that final event. -/
theorem measure_normalizedEndpoints_inter_le_corridors_inter_add_sum_largeDeviation
    (incrementLaw : Measure (ℕ → ℝ))
    {blocks length : ℕ} {scale radius : ℝ} (hscale : 0 < scale)
    (hradius : 0 ≤ radius)
    (lower upper : ℕ → ℝ) (final : Set (ℕ → ℝ)) :
    incrementLaw ({increment | ∀ j < blocks,
        partialSum (j * length) increment / scale ∈
          Set.Ioo (lower j + radius) (upper j - radius)} ∩ final) ≤
      incrementLaw ({increment | ∀ j < blocks, ∀ k ≤ length,
          partialSum (j * length + k) increment ∈
            Set.Icc (scale * lower j) (scale * upper j)} ∩ final) +
        ∑ j ∈ Finset.range blocks,
          incrementLaw {increment |
            ∃ k ∈ Finset.range (length + 1),
              scale * radius ≤
                |blockSum (j * length) (k + 1) increment|} := by
  calc
    _ ≤ incrementLaw ({increment | ∀ j < blocks,
          scale * lower j + scale * radius ≤
              partialSum (j * length) increment ∧
            partialSum (j * length) increment ≤
              scale * upper j - scale * radius} ∩ final) := by
      apply measure_mono
      rintro increment ⟨hendpoints, hfinal⟩
      exact ⟨partitionStartMargins_of_normalizedEndpoints
        hscale hendpoints, hfinal⟩
    _ ≤ _ :=
      measure_partitionStartMargins_inter_le_corridors_inter_add_sum_largeDeviation
        incrementLaw (mul_nonneg hscale.le hradius)
        (fun j => scale * lower j) (fun j => scale * upper j) final

end ProbabilityTheory.RandomWalk

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Corridor.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Probability bounds for block corridors

The deterministic endpoint-margin dichotomy is converted here into a measure
inequality.  No independence or moment assumption is used at this layer.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk


/-- The probability of a block-start margin is bounded by the probability of
staying inside the block corridor plus that of a large relative displacement.
-/
theorem measure_startMargin_le_blockCorridor_add_largeDeviation
    (incrementLaw : Measure (ℕ → ℝ))
    {lower upper radius : ℝ} (hradius : 0 ≤ radius)
    (start length : ℕ) :
    incrementLaw {increment |
        lower + radius ≤ AdditivePath.displacement start increment ∧
          AdditivePath.displacement start increment ≤ upper - radius} ≤
      incrementLaw {increment | ∀ k ≤ length,
          AdditivePath.displacement (start + k) increment ∈ Set.Icc lower upper} +
        incrementLaw {increment |
          ∃ k ∈ Finset.range (length + 1),
            radius ≤ |AdditivePath.blockSum start (k + 1) increment|} := by
  calc
    _ ≤ incrementLaw
        ({increment | ∀ k ≤ length,
            AdditivePath.displacement (start + k) increment ∈ Set.Icc lower upper} ∪
          {increment | ∃ k ∈ Finset.range (length + 1),
            radius ≤ |AdditivePath.blockSum start (k + 1) increment|}) :=
      measure_mono
        (startMargin_subset_blockCorridor_union_largeDeviation
          hradius start length)
    _ ≤ _ := measure_union_le _ _

end ProbabilityTheory.RandomWalk

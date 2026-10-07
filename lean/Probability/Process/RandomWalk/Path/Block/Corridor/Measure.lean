/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Corridor.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Topology.Algebra.BigOperators.PartialSum

/-!
# Measurability of finite-block corridor events

The finite partial-sum corridor is a deterministic block-path predicate.
This file supplies its product-measurable event interface.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

/-- A finite block's strict partial-sum corridor is measurable in the product
sigma algebra on its increment coordinates. -/
theorem measurableSet_inOpenPartialSumCorridor
    {length : ℕ} (lower upper : ℝ) :
    MeasurableSet {block : Fin length → ℝ |
      InOpenPartialSumCorridor lower upper block} := by
  rw [show {block : Fin length → ℝ |
      InOpenPartialSumCorridor lower upper block} =
      ⋂ k : Fin (length + 1),
        {block : Fin length → ℝ |
          Fin.partialSum block k ∈ Set.Ioo lower upper} by
    ext block
    simp [InOpenPartialSumCorridor, Set.mem_Ioo]]
  exact MeasurableSet.iInter fun k =>
      (measurableSet_Ioi.preimage (by fun_prop)).inter
      (measurableSet_Iio.preimage (by fun_prop))

/-- A finite block's strict partial-sum corridor with an open endpoint
window is measurable in the product sigma algebra on its increment
coordinates. -/
theorem measurableSet_inOpenPartialSumCorridorEndsIn
    {length : ℕ} (lower upper endLower endUpper : ℝ) :
    MeasurableSet {block : Fin length → ℝ |
      InOpenPartialSumCorridorEndsIn lower upper endLower endUpper block} := by
  rw [show {block : Fin length → ℝ |
      InOpenPartialSumCorridorEndsIn lower upper endLower endUpper block} =
      {block : Fin length → ℝ | InOpenPartialSumCorridor lower upper block} ∩
        {block : Fin length → ℝ |
          Fin.partialSum block (Fin.last length) ∈ Set.Ioo endLower endUpper} by
    ext block
    simp [InOpenPartialSumCorridorEndsIn]]
  exact (measurableSet_inOpenPartialSumCorridor lower upper).inter <|
    (measurableSet_Ioi.preimage (by fun_prop)).inter
      (measurableSet_Iio.preimage (by fun_prop))

end ProbabilityTheory.RandomWalk

end

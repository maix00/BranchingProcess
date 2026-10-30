/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.SmallDeviation.PathClass.StepCorridor.Partition.Lower.Kernel

/-!
# Core-return event on a stable partition cell

For neighboring endpoint cores `(center i₀, radius i₀)` and
`(center i₁, radius i₁)`, `commonPartitionCellCoreReturnEvent` is the scaled
cell event with its translated return interval centered at `center i₁ -
center i₀` and half-width `(radius i₁ - radius i₀) / 2`. This is the local
cell event appearing in the finite-partition probability lower bound.

## Public declarations

* `commonPartitionCellCoreReturnEvent` defines the event for one partition
  cell from the scaled inner corridor and the endpoint return window described
  above.
-/

@[expose] public section

namespace ProbabilityTheory

open Skorokhod.PathClass.StepCorridor

/-- On one cell, the increment corridor is contracted by the incoming core;
the return window is centered at the displacement between adjacent core
centers and has half the increase in core radius. -/
def commonPartitionCellCoreReturnEvent
    {α : ℝ} (scale : ℝ) (upper lower : StepBoundary)
    (center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ)
    (innerLower innerUpper :
      Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    Set (CadlagPath unitInterval ℝ) := by
  let i₀ := commonPartitionCellLeftKnotIndex upper lower i
  let i₁ := commonPartitionCellRightKnotIndex upper lower i
  let band := (radius i₁ - radius i₀) / 2
  exact scaledNormalizedCellIocReturnEvent (α := α) upper lower i
    (scale / commonPartitionCellSpatialScale α upper lower i)
    (innerLower i + radius i₀ - center i₀)
    (innerUpper i - radius i₀ - center i₀)
    (center i₁ - center i₀ - band)
    (center i₁ - center i₀ + band)


end ProbabilityTheory

end

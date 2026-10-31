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
  For boundaries `upper`, `lower`, and cell \(i\), put
  \[
  i_0=\operatorname{commonPartitionCellLeftKnotIndex}(\mathrm{upper},\mathrm{lower},i),
  \quad i_1=\operatorname{commonPartitionCellRightKnotIndex}
  (\mathrm{upper},\mathrm{lower},i),
  \quad s_i=\operatorname{commonPartitionCellSpatialScale}
  (\alpha,\mathrm{upper},\mathrm{lower},i),
  \quad b=\frac{r_{i_1}-r_{i_0}}{2},
  \]
  where \(c_j=\operatorname{center}(j)\), \(r_j=\operatorname{radius}(j)\),
  \(\ell_i=\operatorname{innerLower}(i)\), \(u_i=\operatorname{innerUpper}(i)\),
  and \(a=\operatorname{scale}\). The complete defining equation is
  \[
  E_i=\operatorname{scaledNormalizedCellIocReturnEvent}_{\alpha}
  (\mathrm{upper},\mathrm{lower},i,a/s_i,
  \ell_i+r_{i_0}-c_{i_0},u_i-r_{i_0}-c_{i_0},
  c_{i_1}-c_{i_0}-b,c_{i_1}-c_{i_0}+b).
  \]
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

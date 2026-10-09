/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.Brownian
public import Probability.Process.Stable.PathLaw.LinearTube

/-!
# Brownian linear-tube corollaries

The Gaussian stable path-law argument is proved in
`Probability.Process.Stable.PathLaw.LinearTube`. These results retain the
Brownian-process interface as corollaries without duplicating the support
argument.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory

/-- A Brownian path has positive probability to remain in any uniform tube
around any linear path on `[0,1]`. -/
theorem IsBrownianReal.measure_linearTube_pos
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (slope width : ℝ) (hwidth : 0 < width) :
    0 < P (fullSegmentCorridorEvent
      (fun t ω => B t ω - slope * (t : ℝ)) 0 1 (-width) width) := by
  exact hB.isStableLevyProcess.measure_linearTube_pos slope width hwidth

/-- The Brownian path law assigns positive mass to every `J₁` ball centered
at a linear path. -/
theorem IsBrownianReal.measure_pathLaw_linearBall_pos
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (slope radius : ℝ) (hradius : 0 < radius) :
    0 < Process.Path.Cadlag.pathLaw P
      (fun t ω => B (UnitInterval.toNNReal t) ω)
      (fun t => hB.toIsPreBrownianReal.aemeasurable
        (UnitInterval.toNNReal t))
      (Metric.ball (Skorokhod.linearPath slope) radius) := by
  simpa only [Process.Path.Cadlag.pathLaw] using
    hB.isStableLevyProcess.measure_pathLaw_linearBall_pos slope radius hradius

end ProbabilityTheory

end

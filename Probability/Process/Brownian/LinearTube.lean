/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.Brownian
public import Probability.Process.Stable.PathLaw.LinearTube
public import Probability.Process.Path.Cadlag.MeasurableMap

/-!
# Brownian linear-tube corollaries

The public theorems in this file are:

- `IsBrownianReal.measure_linearTube_pos`:
  $\mathbb P(\sup_{0\le t\le1}|B_t-st|<r)>0$ for $r>0$.
- `IsBrownianReal.measure_pathLaw_linearBall_pos`:
  the Skorokhod path law gives positive mass to every ball centered at
  $t\mapsto st$.
- `IsBrownianReal.measure_cadlagunitIntervalPathLaw_linearBall_pos`:
  the same assertion for a chosen everywhere-continuous path version.

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

/-- The law of an everywhere-continuous Brownian version assigns positive
mass to every `J₁` ball centered at a linear path. -/
theorem IsBrownianReal.measure_cadlagunitIntervalPathLaw_linearBall_pos
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (slope radius : ℝ) (hradius : 0 < radius) :
    0 < cadlagunitIntervalPathLaw P B hcontinuous hmeasurable
      (Metric.ball (Skorokhod.linearPath slope) radius) := by
  have hpos := hB.measure_pathLaw_linearBall_pos slope radius hradius
  rw [Process.Path.Cadlag.pathLaw_eq_cadlagunitIntervalPathLaw
    P B hcontinuous hmeasurable] at hpos
  exact hpos

end ProbabilityTheory

end

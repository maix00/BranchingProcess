/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.UnitInterval
public import Topology.ContinuousMap.Oscillation

/-!
# Range-oscillation mass of a continuous process

The deterministic oscillation sets and measure-convergence bounds live in the
topology, measure, and convergence layers. This file connects a continuous
process to its path law.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Process.Path

/-- The mass of the range-oscillation set under the continuous-path image of
an arbitrary real-valued process. -/
noncomputable def rangeOscillationMass
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ}
    (hcontinuous : ∀ ω, Continuous (B · ω)) (width : ℝ) : ENNReal :=
  P.map (continuousunitIntervalPath B hcontinuous)
    (ContinuousMap.rangeOscillationSet width)

end ProbabilityTheory.Process.Path

end

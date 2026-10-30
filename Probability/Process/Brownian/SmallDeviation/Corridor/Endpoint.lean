/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Probability.BrownianMotion.Basic
public import Probability.Process.Path.Scaling.UnitInterval
public import Probability.Process.Path.Representation.Skorokhod
public import Probability.Process.Brownian.Construction.PreBrownianModification
public import Topology.Cadlag.Skorokhod.Corridor.Endpoint

import Probability.Process.Brownian.SmallDeviation.Corridor.Bounds

/-!
# Brownian small-deviation bound with a terminal interval

## Public declarations

- `ProbabilityTheory.IsBrownianReal.measure_openCorridor_endsIn_lowerBound`:
  for $w>1$ and $a<-1/2<1/2<b$, a Brownian path remains in
  $(-w/2,w/2)$ and ends in $(a,b)$ with probability at least
  $\exp(-\pi^2/2)$. The proof places the closed unit corridor inside the
  wider open corridor and its terminal interval.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory

/-- The sharp closed-unit-corridor lower bound also applies to every wider
open corridor whose terminal interval contains the closed unit interval. -/
theorem IsBrownianReal.measure_openCorridor_endsIn_lowerBound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsBrownianReal B P)
    {width endpointLower endpointUpper : ℝ}
    (hwidth : 1 < width)
    (hendpointLower : endpointLower < -(1 / 2 : ℝ))
    (hendpointUpper : (1 / 2 : ℝ) < endpointUpper) :
    ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) / 2)) ≤
      P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath (hB.toIsPreBrownianReal.continuousModification)
          (hB.toIsPreBrownianReal.continuous_continuousModification))
        (Skorokhod.rangeInOpenIntervalEndsIn
          (-(width / 2)) (width / 2) endpointLower endpointUpper) := by
  refine (IsBrownianReal.measure_closedUnitCorridor_lowerBound
    hB).trans (measure_mono ?_)
  intro path hpath
  rw [Skorokhod.mem_rangeInOpenIntervalEndsIn_iff]
  constructor
  · refine ⟨(width - 1) / 2, by linarith, fun t => ?_⟩
    have ht := hpath t
    constructor <;> linarith
  · have ht := hpath (⊤ : unitInterval)
    exact ⟨lt_of_lt_of_le hendpointLower ht.1,
      lt_of_le_of_lt ht.2 hendpointUpper⟩


end ProbabilityTheory

end

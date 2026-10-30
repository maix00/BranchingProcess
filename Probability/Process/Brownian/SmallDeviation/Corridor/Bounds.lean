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
public import Topology.Cadlag.Skorokhod.Corridor.Basic
import all Probability.Process.Brownian.SmallDeviation.Corridor.Lemmas.LowerBound

/-!
# Brownian small-deviation bounds for centered corridors

## Public declarations

- `ProbabilityTheory.IsBrownianReal.measure_closedUnitCorridor_lowerBound_of_rho`:
  for $0<\rho<1$, a Brownian motion started at zero remains in
  $[-1/2,1/2]$ with probability at least $\exp(-\pi^2/(2\rho^2))$.
- `ProbabilityTheory.IsBrownianReal.measure_closedCorridor_lowerBound_of_rho_width`:
  for $0<\rho<1$ and $w>0$, the probability of remaining in
  $[-w/2,w/2]$ is at least $\exp(-\pi^2/(2\rho^2w^2))$.
- `ProbabilityTheory.IsBrownianReal.measure_closedUnitCorridor_lowerBound`:
  the closed unit corridor has probability at least $\exp(-\pi^2/2)$.
- `ProbabilityTheory.IsBrownianReal.measure_openCorridor_lowerBound`:
  for $w>1$, the open corridor $(-w/2,w/2)$ has probability at least
  $\exp(-\pi^2/2)$.
- `ProbabilityTheory.IsBrownianReal.measure_closedUnitCorridor_ne_zero`:
  the closed unit corridor has positive probability.

Each result takes only a Brownian process in Mathlib's `IsBrownianReal` sense.
The corridor event is evaluated on a selected measurable continuous
modification, so no extra coordinate-measurability or path-continuity
hypothesis is required. The proof obtains the quantitative bound from the
principal eigenvalue estimate for the centered Rademacher walk and the
closed-event Donsker--Portmanteau bound. The supporting proof chain is kept in
`Probability/Process/Brownian/SmallDeviation/Corridor/Lemmas/LowerBound.lean`.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval

@[expose] public section

namespace ProbabilityTheory

/-- A centered lattice tube occupying a fraction `rho` of the unit corridor
gives the corresponding principal-mode lower bound for the closed Brownian
unit corridor. The event is evaluated on the measurable continuous
modification of the Brownian process. -/
theorem IsBrownianReal.measure_closedUnitCorridor_lowerBound_of_rho
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    {rho : ℝ} (hrho : 0 < rho) (hrho_one : rho < 1)
    (hB : IsBrownianReal B P) :
    ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) / (2 * rho ^ 2))) ≤
      P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath (hB.toIsPreBrownianReal.continuousModification)
          (hB.toIsPreBrownianReal.continuous_continuousModification))
        (Skorokhod.rangeInClosedInterval (-(1 / 2 : ℝ)) (1 / 2)) := by
  exact closedUnitCorridorLowerBoundOfRhoCore hrho hrho_one hB

/-- The corresponding principal-mode bound for a centered closed corridor of
arbitrary positive width. -/
theorem IsBrownianReal.measure_closedCorridor_lowerBound_of_rho_width
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    {rho width : ℝ} (hrho : 0 < rho) (hrho_one : rho < 1)
    (hwidth : 0 < width)
    (hB : IsBrownianReal B P) :
    ENNReal.ofReal (Real.exp
      (-(Real.pi ^ 2) / (2 * rho ^ 2 * width ^ 2))) ≤
      P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath (hB.toIsPreBrownianReal.continuousModification)
          (hB.toIsPreBrownianReal.continuous_continuousModification))
        (Skorokhod.rangeInClosedInterval (-(width / 2)) (width / 2)) := by
  exact closedCorridorLowerBoundOfRhoWidthCore
    hrho hrho_one hwidth hB

/-- The sharp principal-exponent lower bound for the closed centered unit
corridor of a Brownian process. -/
theorem IsBrownianReal.measure_closedUnitCorridor_lowerBound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsBrownianReal B P) :
    ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) / 2)) ≤
      P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath (hB.toIsPreBrownianReal.continuousModification)
          (hB.toIsPreBrownianReal.continuous_continuousModification))
        (Skorokhod.rangeInClosedInterval (-(1 / 2 : ℝ)) (1 / 2)) := by
  exact closedUnitCorridorLowerBoundCore hB

/-- The closed-unit-corridor lower bound also applies to any strictly wider
open centered corridor. -/
theorem IsBrownianReal.measure_openCorridor_lowerBound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsBrownianReal B P)
    {width : ℝ} (hwidth : 1 < width) :
    ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) / 2)) ≤
      P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath (hB.toIsPreBrownianReal.continuousModification)
          (hB.toIsPreBrownianReal.continuous_continuousModification))
        (Skorokhod.rangeInOpenInterval (-(width / 2)) (width / 2)) := by
  exact openCorridorLowerBoundCore hB hwidth

/-- The closed centered Brownian unit corridor has positive probability. -/
theorem IsBrownianReal.measure_closedUnitCorridor_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsBrownianReal B P) :
    P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath (hB.toIsPreBrownianReal.continuousModification)
          (hB.toIsPreBrownianReal.continuous_continuousModification))
        (Skorokhod.rangeInClosedInterval (-(1 / 2 : ℝ)) (1 / 2)) ≠ 0 := by
  exact closedUnitCorridorNeZeroCore hB

end ProbabilityTheory

end

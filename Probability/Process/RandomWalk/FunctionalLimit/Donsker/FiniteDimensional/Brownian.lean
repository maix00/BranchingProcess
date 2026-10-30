/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.AdditivePath.Basic
public import Analysis.Asymptotics.Scale.Block.Proportional
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.BrownianMotion.Basic
public import Probability.Process.Brownian.FiniteDimensional.UniformGrid
public import Probability.Sequence.IID.Basic
import Probability.Process.RandomWalk.FunctionalLimit.Donsker.FiniteDimensional.Basic
import Probability.ConvergenceInDistribution.Basic

/-!
# Random-walk limits on Brownian uniform grids

## Public declarations

- `ProbabilityTheory.RandomWalk.tendstoInDistribution_proportionalBlockEndpoints_brownian`:
  for centered, unit-second-moment increments, normalized random-walk
  positions on a fixed equal partition converge jointly to the corresponding
  values of any pre-Brownian process.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Asymptotics

/-- Equal-partition random-walk endpoints converge jointly to Brownian values
at the matching uniform grid. -/
theorem tendstoInDistribution_proportionalBlockEndpoints_brownian
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hcentered : ∫ x, x ∂nu = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂nu = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    {fraction : ℝ} (hfraction : 0 < fraction) (blocks : ℕ) :
    TendstoInDistribution
      (fun n increment (j : Fin (blocks + 1)) =>
        AdditivePath.displacement (j * proportionalBlockLength fraction n) increment /
          Real.sqrt n)
      atTop
      (fun ω => fun j : Fin (blocks + 1) =>
        B (uniformGridTime ⟨fraction, hfraction.le⟩ j) ω)
      (fun _ => iidSequenceLaw nu) P := by
  have h := tendstoInDistribution_proportionalBlockEndpoints nu hcentered
    hsecondMoment hfraction blocks
  exact h.congr_limit_hasLaw (by
    convert hB.hasLaw_uniformGrid_of_standardGaussian ⟨fraction, hfraction.le⟩ blocks
      using 1
    congr 1)

end ProbabilityTheory.RandomWalk

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Step.PointMeasure.Basic

/-!
# Integration under the point-measure law

The point-measure law of a random step presentation is defined in
`Step/PointMeasure/Basic.lean` as a pushforward. This file gives its integral
formula for measurable functionals.

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.lintegral_stepPointMeasure`: for
  measurable $F$, integrating $F$ under the point-measure law equals the
  expectation of $F$ evaluated at the sample's point measure.

-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

theorem lintegral_stepPointMeasure
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] (S : StepPresentation Ω ι X) (P : Measure Ω)
    (F : Measure X → ENNReal) (hF : Measurable F) :
    ∫⁻ η, F η ∂(S.branchingLaw P) =
      ∫⁻ ω, F (stepPointMeasure (S ω)) ∂P := by
  unfold StepPresentation.branchingLaw
  exact MeasureTheory.lintegral_map
    hF S.pointMeasure_measurable

end ProbabilityTheory.BranchingRandomWalk

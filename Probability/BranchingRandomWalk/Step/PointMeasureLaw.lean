/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Step.Presentation
public import Probability.BranchingRandomWalk.Step.PointMeasure

/-!
# Laws of deterministic point-measure observations

These are pushforward identities for the point measure of `S`. They are kept
separate from the branching-random-walk many-to-one theorem, which concerns a
size-biased spine path across generations.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

theorem stepPointMeasureLaw_forward
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] (S : StepPresentation Ω ι X) (P : Measure Ω) :
    (S.indexedLaw P).map stepPointMeasure = S.branchingLaw P :=
  S.indexedLaw_map_pointMeasure P

theorem stepPointMeasureLaw_backward
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] (S : StepPresentation Ω ι X) (P : Measure Ω) :
    S.branchingLaw P = (S.indexedLaw P).map stepPointMeasure :=
  (S.indexedLaw_map_pointMeasure P).symm

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

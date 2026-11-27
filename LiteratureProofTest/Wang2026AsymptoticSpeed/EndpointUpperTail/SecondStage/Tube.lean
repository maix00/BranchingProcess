/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily
public import LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.SecondStage.TubeParameters
public import Probability.BranchingRandomWalk.Assumptions.Structural
public import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Event
public import Probability.Process.RandomWalk.Path.Corridor.Affine

/-!
# Second-stage tube and one-root failure events

## Public declarations

- `LiteratureProofTest.Wang2026AsymptoticSpeed.positiveASecondStageCorridor`:
  defines the affine corridor \(\mathcal C_D\) of duration \(D\), slope
  \(d_D\), width \(w_D\), and endpoint \(d_DD+vD^{1/3}\).
- `LiteratureProofTest.Wang2026AsymptoticSpeed.positiveASecondStageFailureEvent`:
  the event that none of the first \(m\) selected roots has a path history in
  \(\mathcal C_D\).
The corridor is the relative tube in the proof of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 4, Theorem 1.1, case $0<a<1$.
-/

@[expose] public section

namespace LiteratureProofTest.Wang2026AsymptoticSpeed

open ProbabilityTheory

open Asymptotics

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- The relative affine tube used for a second-stage descendant tree. -/
noncomputable def positiveASecondStageCorridor
    (D : ℕ) (κ c v : ℝ) : Set (Fin (D + 1) → ℝ) :=
  affineCorridorThrough D 0
    (positiveASecondStageSlope κ c D)
    (positiveASecondStageWidth c D)
    (positiveASecondStageSlope κ c D * (D : ℝ) +
      v * ((D : ℝ) ^ ((1 : ℝ) / 3)))

/-- All roots fail to produce a path through the second-stage tube. -/
def positiveASecondStageFailureEvent
    (m D : ℕ) (κ c v : ℝ) : Set (FiniteRootStepField m ℕ ℝ) :=
  {field | ∀ r : Fin m,
    field r ∉ hasPathHistoryIn (ι := ℕ) realPotential D 0
      (positiveASecondStageCorridor D κ c v)}

end LiteratureProofTest.Wang2026AsymptoticSpeed

end

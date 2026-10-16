/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.Normal.ContinuousBoundary
/-!
# Shared source-corridor definitions for the horizontal-tube rate proof

The proof-internal declarations in this module are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas.constantBoundary`: the constant path $t\mapsto c$ in $C([0,1],\mathbb R)$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas.sourceRelativeConstantCorridorEvent`: the event $\{\omega: W_{n,\mathrm{left}}(\omega)\in\mathcal C(c_-,c_+)\}$ for the terminal-left normalized walk path.

These definitions are shared by the proofs of the closed-tube and endpoint-window forms of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1. They are proof support rather than independent theorem interfaces.
-/

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas

def constantBoundary (value : ℝ) : C(unitInterval, ℝ) :=
  ContinuousMap.const unitInterval value

def sourceRelativeConstantCorridorEvent (scale : ℕ → ℝ) (n : ℕ)
    (lower upper : ℝ) : Set (ℕ → ℝ) :=
  {increment | sourceNormalizedStepCadlagPathIcc scale n increment ∈
    relativeContinuousBoundaryCorridorSet
      (constantBoundary lower) (constantBoundary upper)}


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas

end

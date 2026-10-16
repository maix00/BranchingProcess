/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.Normal.ContinuousBoundary
/-!
# Source-normalized constant corridor events

The public definitions in this module are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas.constantBoundary`: the constant path $t\mapsto c$ in $C([0,1],\mathbb R)$ used in the closed-tube proof.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas.sourceRelativeConstantCorridorEvent`: the event $\{\omega: W_{n,\mathrm{left}}(\omega)\in\mathcal C(c_-,c_+)\}$ for the terminal-left normalized walk path used in the rate comparison.

The event packages the strict source-path corridor used to transfer A. A.
Mogul'skii, Theorem 3, Section 4, p. 764, to the closed-tube and endpoint-window
forms of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with
Infinite Offspring*, Chapter 3, Lemma 3.1(ii). Mogul'skii's article is
“Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755--765; its English translation is “Small
Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas

/-- The constant corridor boundary at height `value`. -/
def constantBoundary (value : ℝ) : C(unitInterval, ℝ) :=
  ContinuousMap.const unitInterval value

/-- The terminal-left normalized walk path lies in the strict corridor
between the two constant boundaries. This is the source-path event used in
the finite-variance closed-tube and endpoint-window rate transfers. -/
def sourceRelativeConstantCorridorEvent (scale : ℕ → ℝ) (n : ℕ)
    (lower upper : ℝ) : Set (ℕ → ℝ) :=
  {increment | sourceNormalizedStepCadlagPathIcc scale n increment ∈
    relativeContinuousBoundaryCorridorSet
      (constantBoundary lower) (constantBoundary upper)}


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas

end

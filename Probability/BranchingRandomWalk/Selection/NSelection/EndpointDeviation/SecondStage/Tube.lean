/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Lemmas.Corridor.PZ
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.TubeParameters
public import Probability.BranchingRandomWalk.Assumptions.CrossWeight
public import Probability.BranchingRandomWalk.Assumptions.Structural
public import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Event
public import Probability.BranchingRandomWalk.Spine.RandomWalk.Basic
public import Probability.BranchingRandomWalk.Spine.Tilted.Law
public import Probability.BranchingRandomWalk.Spine.Tube.MRCA.Expansion
public import Probability.Distributions.Moments.Real
public import Probability.Process.RandomWalk.Path.Basic

/-!
# Second-stage tube and one-root failure events

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.positiveASecondStageCorridor`:
  defines the affine corridor \(\mathcal C_D\) of duration \(D\), slope
  \(d_D\), width \(w_D\), and endpoint \(d_DD+vD^{1/3}\).
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.positiveASecondStageFailureEvent`:
  the event that none of the first \(m\) selected roots has a path history in
  \(\mathcal C_D\).
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.positiveASecondStagePZMean`:
  the one-root Paley--Zygmund ratio formed from the tilted path count's first
  and second moments.

The public definitions are the second-stage corridor, the all-root failure
event, and the one-root Paley--Zygmund ratio used by the terminal failure
bound. The parameterization follows the second-stage construction in
Chapter 3, Lemma 3.5 of WANG Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring*. Write
\(d_D=\texttt{positiveASecondStageSlope}\;\kappa\;c\;D\),
\(w_D=\texttt{positiveASecondStageWidth}\;c\;D\), and
\(U_D=d_DD+vD^{1/3}\). Then
\[
  \mathcal C_D=\operatorname{affineCorridorThrough}(D,0,d_D,w_D,U_D),
  \qquad
  F_{m,D}=\{f:\forall r\in\operatorname{Fin}(m),\;
    f(r)\notin\operatorname{hasPathHistoryIn}(D,0,\mathcal C_D)\}.
\]
For \(E_D=\{x:\operatorname{history}_D(0,x)\in\mathcal C_D\}\),
\(\widetilde\mu=\texttt{tiltedIncrementFieldLaw}\;\texttt{realPotential}\;\mu\),
and \(C_\mu=\int\texttt{crossPotentialWeight}\;\texttt{realPotential}\;(-1)\;\xi\,d\mu(\xi)\),
the ratio is
\[
  q_D=\frac{\widetilde\mu(E_D)^2}
  {e^{U_D}\widetilde\mu(E_D)+
    C_\mu\sum_{j=0}^{D-1}e^{2U_D-d_Dj}
      \widetilde\mu\!\left(\left\{x:
        \operatorname{history}_j(0,x)\in
        \operatorname{affineCorridorPrefix}(j,0,d_D,w_D)\right\}\right)}.
\]
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

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

/-- The explicit one-root PZ ratio for the second-stage tube. -/
noncomputable def positiveASecondStagePZMean
    (μ : Measure (Step ℕ ℝ)) (D : ℕ) (κ c v : ℝ) : ℝ≥0∞ := by
  let drift := positiveASecondStageSlope κ c D
  let width := positiveASecondStageWidth c D
  let endpointUpper := drift * (D : ℝ) + v * ((D : ℝ) ^ ((1 : ℝ) / 3))
  let corridor := positiveASecondStageCorridor D κ c v
  let spineEvent : Set (ℕ → ℝ) :=
    {increment | RandomWalk.history D 0 increment ∈ corridor}
  let lowerMean : ℝ≥0∞ := ENNReal.ofReal (Real.exp (0 - 0)) *
    (tiltedIncrementFieldLaw realPotential μ) spineEvent
  let upperMean : ℝ≥0∞ := ENNReal.ofReal (Real.exp (endpointUpper - 0)) *
    (tiltedIncrementFieldLaw realPotential μ) spineEvent
  let pairBound : ℝ≥0∞ := ∑ j : Fin D,
    ENNReal.ofReal (Real.exp (-(2 * 0))) *
      (ENNReal.ofReal (Real.exp (2 * endpointUpper)) * (1 : ℝ≥0∞) ^ 2) *
      (∫⁻ ξ, crossPotentialWeight realPotential (-1) ξ ∂μ) *
      (ENNReal.ofReal (Real.exp (0 - (0 + drift * (j.val : ℝ)))) *
        (tiltedIncrementFieldLaw realPotential μ)
          {increment | RandomWalk.history j.val 0 increment ∈
            affineCorridorPrefix j.val 0 drift width})
  exact lowerMean ^ 2 / (upperMean + pairBound)


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

end

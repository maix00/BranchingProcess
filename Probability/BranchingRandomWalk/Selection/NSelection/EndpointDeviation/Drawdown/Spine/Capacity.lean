/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity.Spine
import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Event
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.PairBound

/-!
# First-stage killed-population count bound

The public declaration is
`ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rightTailPositiveAFirstStageLowCount_le_of_affineCorridorDrawdown`.
For a generation-$n$ affine corridor $G_n$ with positive tilted-walk
probability, a drawdown bound $q_j$ on every prefix yields a second-moment
bound for the number $N_{G_n}$ of roots whose paths stay in $G_n$. Write
$\nu$ for the tilted increment law,
$M_-=e^{\mathrm{lower}-\mathrm{initial}}\nu(G_n)$,
$M_+=e^{\mathrm{endpointUpper}-\mathrm{initial}}\nu(G_n)$, and $R$ for
the explicit distinct-pair sum in the theorem statement. Then the event
$N_{G_n}\leq \Lambda$ has probability at most $e^{-\Lambda}$, where
\[\Lambda=\frac{m}{4}\left(\frac{M_-^2}{M_++R}\right)_{\!\mathrm{toReal}}.\]
The hypotheses and the pair-sum formula for $R$ are stated explicitly in the
Lean theorem.

The proof follows the affine-corridor second-moment argument used for the
positive-initial-mass estimate in Proposition 3.1, equation (4.15), of
Elie Aïdékon and Yueyun Hu, *Average-weight percolation on the complete
graph*, arXiv:2512.23266 (2025).
-/
open Filter MeasureTheory
open scoped ENNReal BigOperators Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- The affine-corridor first-stage count estimate with its second moment
derived from the actual distinct-pair count.  The pair estimate uses the
the finite cross-weight condition and the stated tilted-walk drawdown
bounds; callers do not supply a second-moment bound for the path count. -/
theorem measure_rightTailPositiveAFirstStageLowCount_le_of_affineCorridorDrawdown
    (m horizon : ℕ) (hm : 0 < m) (initial lower drift width endpointUpper : ℝ)
    (hdrift : 0 ≤ drift)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hcross : HasFiniteCrossWeight realPotential μ)
    (q : ℕ → ℝ≥0∞)
    (hqTop : ∀ n, q n ≠ ∞)
    (hdrawdown : ∀ n,
      (tiltedIncrementFieldLaw realPotential μ)
        (RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          n width (width + drift * (n : ℝ))) ≤ q n)
    (hspinePositive : 0 < (tiltedIncrementFieldLaw realPotential μ)
      {increment | RandomWalk.history horizon initial increment ∈
        affineCorridorThrough horizon lower drift width endpointUpper})
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)] :
    let corridor := affineCorridorThrough horizon lower drift width endpointUpper
    let spineEvent := {increment : ℕ → ℝ |
      RandomWalk.history horizon initial increment ∈ corridor}
    let lowerMean := ENNReal.ofReal (Real.exp (lower - initial)) *
      (tiltedIncrementFieldLaw realPotential μ) spineEvent
    let upperMean := ENNReal.ofReal (Real.exp (endpointUpper - initial)) *
      (tiltedIncrementFieldLaw realPotential μ) spineEvent
    let pairBound := ∑ j : Fin horizon,
      ENNReal.ofReal (Real.exp (-(2 * initial))) *
        (ENNReal.ofReal (Real.exp (2 * endpointUpper)) *
          q (horizon - j.val - 1) ^ 2) *
        (∫⁻ ξ, crossChildWeight realPotential ξ ∂μ) *
        (ENNReal.ofReal
          (Real.exp (initial - (lower + drift * (j.val : ℝ)))) *
          (tiltedIncrementFieldLaw realPotential μ)
            {increment | RandomWalk.history j.val initial increment ∈
              affineCorridorPrefix j.val lower drift width})
    (finiteRootStepFieldLaw μ m)
      {field : FiniteRootStepField m ℕ ℝ |
        (∑ r : Fin m,
          (hasPathHistoryIn (ι := ℕ) realPotential horizon initial corridor).indicator
            (fun _ => (1 : ℝ)) (field r)) ≤
          (m : ℝ) * (lowerMean ^ 2 / (upperMean + pairBound)).toReal / 4} ≤
        ENNReal.ofReal (Real.exp
          (-((m : ℝ) * (lowerMean ^ 2 /
            (upperMean + pairBound)).toReal / 4))) := by
  classical
  let corridor := affineCorridorThrough horizon lower drift width endpointUpper
  let spineEvent : Set (ℕ → ℝ) :=
    {increment | RandomWalk.history horizon initial increment ∈ corridor}
  let lowerMean : ℝ≥0∞ := ENNReal.ofReal (Real.exp (lower - initial)) *
    (tiltedIncrementFieldLaw realPotential μ) spineEvent
  let upperMean : ℝ≥0∞ := ENNReal.ofReal (Real.exp (endpointUpper - initial)) *
    (tiltedIncrementFieldLaw realPotential μ) spineEvent
  let pairBound : ℝ≥0∞ := ∑ j : Fin horizon,
    ENNReal.ofReal (Real.exp (-(2 * initial))) *
      (ENNReal.ofReal (Real.exp (2 * endpointUpper)) *
        q (horizon - j.val - 1) ^ 2) *
      (∫⁻ ξ, crossChildWeight realPotential ξ ∂μ) *
      (ENNReal.ofReal
        (Real.exp (initial - (lower + drift * (j.val : ℝ)))) *
        (tiltedIncrementFieldLaw realPotential μ)
          {increment | RandomWalk.history j.val initial increment ∈
            affineCorridorPrefix j.val lower drift width})
  have hcorridor : MeasurableSet corridor :=
    measurableSet_affineCorridorThrough horizon lower drift width endpointUpper
  have hterminalLower : ∀ history ∈ corridor,
      lower ≤ history ⟨horizon, Nat.lt_succ_self horizon⟩ := by
    intro history hhistory
    calc
      lower ≤ lower + drift * (horizon : ℝ) := by
        exact le_add_of_nonneg_right
          (mul_nonneg hdrift (by positivity : 0 ≤ (horizon : ℝ)))
      _ ≤ history ⟨horizon, Nat.lt_succ_self horizon⟩ := by
        exact (hhistory.1 ⟨horizon, Nat.lt_succ_self horizon⟩).1
  have hterminalUpper : ∀ history ∈ corridor,
      history ⟨horizon, Nat.lt_succ_self horizon⟩ ≤ endpointUpper := by
    intro history hhistory
    exact hhistory.2
  have hpairBound :
      (∫⁻ ω, pathGenerationDistinctAddressPairCount realPotential horizon
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω
        ∂stepFieldLaw μ) ≤ pairBound := by
    simpa [pairBound, corridor] using
      (Spine.lintegral_pathGenerationDistinctAddressPairCount_affineCorridor_le_of_drawdown
        realPotential μ hboundary horizon initial lower drift width endpointUpper
        hdrift q hdrawdown)
  have htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw realPotential μ) :=
    tiltedIncrementFieldLaw_isProbability realPotential μ hboundary
  letI : IsProbabilityMeasure (tiltedIncrementFieldLaw realPotential μ) := htilted
  have hpairBoundTop : pairBound ≠ ∞ := by
    dsimp [pairBound]
    apply ENNReal.sum_ne_top.2
    intro j _hj
    have hqj : q (horizon - j.val - 1) ≠ ∞ := hqTop _
    have hqjSq : q (horizon - j.val - 1) ^ 2 ≠ ∞ :=
      ENNReal.pow_ne_top hqj
    have hprefix :
        (tiltedIncrementFieldLaw realPotential μ)
          {increment | RandomWalk.history j.val initial increment ∈
            affineCorridorPrefix j.val lower drift width} ≠ ∞ :=
      measure_ne_top _ _
    have hfirst : ENNReal.ofReal (Real.exp (-(2 * initial))) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    have hsecond : ENNReal.ofReal (Real.exp (2 * endpointUpper)) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    have hcrossIntegral :
        (∫⁻ ξ, crossChildWeight realPotential ξ ∂μ) ≠ ∞ := hcross
    have hlast : ENNReal.ofReal
          (Real.exp (initial - (lower + drift * (j.val : ℝ)))) *
          (tiltedIncrementFieldLaw realPotential μ)
            {increment | RandomWalk.history j.val initial increment ∈
              affineCorridorPrefix j.val lower drift width} ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hprefix
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.mul_ne_top hfirst
          (ENNReal.mul_ne_top hsecond hqjSq)
      · exact hcrossIntegral
    · exact hlast
  simpa [corridor, spineEvent, lowerMean, upperMean, pairBound] using
    (Spine.measure_finiteRootCorridorCount_le_quarter_spineLower_of_pairMoment
      realPotential μ hboundary horizon initial lower endpointUpper corridor
      hcorridor hterminalLower hterminalUpper m hm pairBound hpairBound
      hpairBoundTop hspinePositive)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

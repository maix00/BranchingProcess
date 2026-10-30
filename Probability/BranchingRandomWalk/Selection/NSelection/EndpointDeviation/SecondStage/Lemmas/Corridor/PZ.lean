/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Lemmas.Corridor.Parameterization
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Capacity
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.TubeParameters
/-!
# Second-stage tube survival from the affine-corridor PZ estimate

## Internal proof declarations


The proof-chain lemma used in `SecondStage/Roots/Lemmas/AllAvoid.lean`,
`eventually_measure_positiveASecondStage_allRootsAvoid_le_of_centeredSecondMoment`,
combines the spine lower bound and the MRCA pair estimate. For all sufficiently
large horizons, it gives
\[
  \mathbb P(\text{each of the $m$ roots fails})
  \le
  \exp\!\left(-\frac{m}{4}
    \left(\frac{M_-^2}{M_+ + Q}\right)_{\!\mathrm{toReal}}\right),
\]
where $M_-$ and $M_+$ are the lower and upper first-moment bounds and $Q$ is
the summed MRCA pair bound in the theorem statement.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.UlamHarris
open Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Entrance
open ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

private lemma positiveASecondStageSpineLowerBound_pos
    (ν : Measure ℝ) (κ c v : ℝ) (entryQ : ℝ≥0∞) (C : ℝ)
    (bridgeQ : ℝ≥0∞) (amplitude : ℝ) (D : ℕ)
    (hentryQ : 0 < entryQ) (hbridgeQ : 0 < bridgeQ) :
    0 < positiveASecondStageSpineLowerBound
      ν κ c v entryQ C bridgeQ amplitude D := by
  dsimp [positiveASecondStageSpineLowerBound]
  let lambda : ℝ := κ / c ^ 2
  let α : ℝ := (5 * lambda + v) / 2
  let β : ℝ := (v - lambda) / 24
  let scale : ℕ → ℝ := fun k => β * ((k : ℝ) ^ ((1 : ℝ) / 3))
  let entranceScale : ℝ := α * ((D : ℝ) ^ ((1 : ℝ) / 3))
  let bridgeLength : ℕ := D - ⌊entranceScale ^ 2⌋₊
  have hbase : 0 < ENNReal.ofReal (Real.exp
      ((C / ((2 / 2 - 13 / 60) ^ (2 : ℝ)) - 1) * amplitude ^ (2 : ℝ))) := by
    apply ENNReal.ofReal_pos.mpr
    exact Real.exp_pos _
  have hpower := ENNReal.pow_pos hbase
    (Combinatorics.Sequence.balancedBlockCount
      (finiteVarianceBridgeLength scale bridgeLength -
        stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) scale bridgeLength)
      (stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) scale bridgeLength) + 1)
  have hentryDiv : 0 < entryQ / (⌊entranceScale ^ 2⌋₊ : ℝ≥0∞) := by
    apply ENNReal.div_pos (ne_of_gt hentryQ)
    finiteness
  have hbridgeDiv : 0 < bridgeQ /
      (finiteVarianceEntranceLength scale bridgeLength : ℝ≥0∞) := by
    apply ENNReal.div_pos (ne_of_gt hbridgeQ)
    finiteness
  exact ENNReal.mul_pos
    (ne_of_gt (ENNReal.mul_pos hentryDiv.ne' hpower.ne')) hbridgeDiv.ne'

/-- For the second-stage parameter scales, the probability that all
independent initial roots fail to produce a path through the second-stage
corridor is bounded by the PZ/Chernoff exponential.  The PZ mean is left
explicit so the polynomial budget can be checked separately.  No extra
random-walk or drawdown hypothesis is assumed: centered finite second moment
gives the spine corridor lower bound, and the MRCA estimate uses `q = 1`. -/
lemma eventually_measure_positiveASecondStage_allRootsAvoid_le_of_centeredSecondMoment
    {D : ℕ → ℕ} (hD : Tendsto (fun n => (D n : ℝ)) atTop atTop)
    (μ : Measure (Combinatorics.Branching.Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hcross : HasFiniteCrossWeight realPotential μ)
    {sigma κ c v : ℝ}
    (hν : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) μ) (sigma ^ 2))
    (hsigma : 0 < sigma) (hκ : 0 ≤ κ) (hc : 0 < c) (hv : 0 < v)
    (hκv : κ / c ^ 2 < v)
    (hterminal : κ / c ^ 2 ≤ 2 * v / 5)
    (hentranceWidth : (5 * (κ / c ^ 2) + v) / 2 ≤ c)
    (m : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)] :
    ∃ entryQ : ℝ≥0∞, 0 < entryQ ∧
      ∃ C : ℝ, C < 0 ∧ ∃ bridgeQ : ℝ≥0∞, 0 < bridgeQ ∧
        ∃ amplitude : ℝ, 0 < amplitude ∧
          ∀ᶠ n : ℕ in atTop,
            let drift := positiveASecondStageSlope κ c (D n)
            let width := positiveASecondStageWidth c (D n)
            let terminalExtra := v * ((D n : ℝ) ^ ((1 : ℝ) / 3))
            let endpointUpper := drift * (D n : ℝ) + terminalExtra
            let corridor := affineCorridorThrough (D n) 0 drift width endpointUpper
            let spineEvent : Set (ℕ → ℝ) :=
              {increment | RandomWalk.history (D n) 0 increment ∈ corridor}
            let lowerMean := ENNReal.ofReal (Real.exp (0 - 0)) *
              (tiltedIncrementFieldLaw realPotential μ) spineEvent
            let upperMean := ENNReal.ofReal (Real.exp (endpointUpper - 0)) *
              (tiltedIncrementFieldLaw realPotential μ) spineEvent
            let pairBound := ∑ j : Fin (D n),
              ENNReal.ofReal (Real.exp (-(2 * 0))) *
                (ENNReal.ofReal (Real.exp (2 * endpointUpper)) *
                  (1 : ℝ≥0∞) ^ 2) *
                (∫⁻ ξ, crossPotentialWeight realPotential (-1) ξ ∂μ) *
                (ENNReal.ofReal (Real.exp (0 - (0 + drift * (j.val : ℝ)))) *
                  (tiltedIncrementFieldLaw realPotential μ)
                    {increment | RandomWalk.history j.val 0 increment ∈
                      affineCorridorPrefix j.val 0 drift width})
            let pzMean := lowerMean ^ 2 / (upperMean + pairBound)
            (finiteRootStepFieldLaw μ m)
              {field : FiniteRootStepField m ℕ ℝ |
                ∀ r : Fin m,
                  field r ∉ hasPathHistoryIn (ι := ℕ) realPotential (D n) 0 corridor} ≤
              ENNReal.ofReal (Real.exp (-((m : ℝ) * pzMean.toReal / 4))) := by
  let ν : Measure ℝ := tiltedPotentialLaw realPotential (-1) μ
  have : IsProbabilityMeasure ν :=
    tiltedPotentialLaw_isProbability realPotential μ hboundary
  have hν_eq : ν = tiltedPotentialLaw realPotential (-1) μ := rfl
  obtain ⟨entryQ, hentryQ, C, hC, bridgeQ, hbridgeQ, amplitude, hamplitude,
      hspineLower⟩ :=
    eventually_iidSequenceLaw_positiveASecondStageAffineCorridor_lowerBound_of_centeredSecondMoment
      (D := D) hD ν hν hsigma hκ hc hv hκv hterminal hentranceWidth
  have hlaw : tiltedIncrementFieldLaw realPotential μ = iidSequenceLaw ν := by
    rw [hν_eq]
    rfl
  have : IsProbabilityMeasure (tiltedIncrementFieldLaw realPotential μ) :=
    tiltedIncrementFieldLaw_isProbability realPotential μ hboundary
  refine ⟨entryQ, hentryQ, C, hC, bridgeQ, hbridgeQ, amplitude, hamplitude, ?_⟩
  filter_upwards [hspineLower] with n hspineLowerN
  let drift := positiveASecondStageSlope κ c (D n)
  let width := positiveASecondStageWidth c (D n)
  let terminalExtra := v * ((D n : ℝ) ^ ((1 : ℝ) / 3))
  let endpointUpper := drift * (D n : ℝ) + terminalExtra
  let corridor := affineCorridorThrough (D n) 0 drift width endpointUpper
  let spineEvent : Set (ℕ → ℝ) :=
    {increment | RandomWalk.history (D n) 0 increment ∈ corridor}
  let lowerMean := ENNReal.ofReal (Real.exp (0 - 0)) *
    (tiltedIncrementFieldLaw realPotential μ) spineEvent
  let upperMean := ENNReal.ofReal (Real.exp (endpointUpper - 0)) *
    (tiltedIncrementFieldLaw realPotential μ) spineEvent
  let pairBound := ∑ j : Fin (D n),
    ENNReal.ofReal (Real.exp (-(2 * 0))) *
      (ENNReal.ofReal (Real.exp (2 * endpointUpper)) * (1 : ℝ≥0∞) ^ 2) *
      (∫⁻ ξ, crossPotentialWeight realPotential (-1) ξ ∂μ) *
      (ENNReal.ofReal (Real.exp (0 - (0 + drift * (j.val : ℝ)))) *
        (tiltedIncrementFieldLaw realPotential μ)
          {increment | RandomWalk.history j.val 0 increment ∈
            affineCorridorPrefix j.val 0 drift width})
  let pzMean := lowerMean ^ 2 / (upperMean + pairBound)
  have hmassPos : 0 < positiveASecondStageSpineLowerBound
      ν κ c v entryQ C bridgeQ amplitude (D n) :=
    positiveASecondStageSpineLowerBound_pos ν κ c v entryQ C bridgeQ
      amplitude (D n) hentryQ hbridgeQ
  have hspine : 0 < (tiltedIncrementFieldLaw realPotential μ) spineEvent := by
    have hbound : positiveASecondStageSpineLowerBound
        ν κ c v entryQ C bridgeQ amplitude (D n) ≤
          iidSequenceLaw ν spineEvent := by
      simpa [spineEvent, corridor, drift, width, endpointUpper, terminalExtra,
        positiveASecondStageSlope, positiveASecondStageWidth]
        using hspineLowerN
    rw [hlaw]
    exact lt_of_lt_of_le hmassPos hbound
  have hdrawdown : ∀ k : ℕ,
      (tiltedIncrementFieldLaw realPotential μ)
        (noLargeDropEndpointBelowEvent k width (width + drift * (k : ℝ))) ≤ 1 := by
    intro k
    calc
      (tiltedIncrementFieldLaw realPotential μ)
          (noLargeDropEndpointBelowEvent k width (width + drift * (k : ℝ))) ≤
        (tiltedIncrementFieldLaw realPotential μ) Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hdrift : 0 ≤ drift := by
    dsimp [drift, positiveASecondStageSlope]
    apply mul_nonneg
    · exact div_nonneg hκ (sq_nonneg c)
    · exact Real.rpow_nonneg (by positivity) _
  have hlowCount :=
    measure_positiveAFirstStageLowCount_le_of_affineCorridorDrawdown
      m (D n) hm 0 0 drift width endpointUpper hdrift
      μ hboundary hcross (fun _ => (1 : ℝ≥0∞)) (by simp)
      (by intro k; simpa using hdrawdown k) hspine
  have havoidSubset :
      {field : FiniteRootStepField m ℕ ℝ |
        ∀ r : Fin m,
          field r ∉ hasPathHistoryIn (ι := ℕ) realPotential (D n) 0 corridor} ⊆
      {field : FiniteRootStepField m ℕ ℝ |
        (∑ r : Fin m,
          (hasPathHistoryIn (ι := ℕ) realPotential (D n) 0 corridor).indicator
            (fun _ => (1 : ℝ)) (field r)) ≤
            (m : ℝ) * pzMean.toReal / 4} := by
    intro field hall
    change (∑ r : Fin m,
      (hasPathHistoryIn (ι := ℕ) realPotential (D n) 0 corridor).indicator
        (fun _ => (1 : ℝ)) (field r)) ≤ (m : ℝ) * pzMean.toReal / 4
    have hzero :
        (∑ r : Fin m,
          (hasPathHistoryIn (ι := ℕ) realPotential (D n) 0 corridor).indicator
            (fun _ => (1 : ℝ)) (field r)) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      simp [Set.indicator, hall r]
    rw [hzero]
    positivity
  have hlowCount' :
      (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ ℝ |
          (∑ r : Fin m,
            (hasPathHistoryIn (ι := ℕ) realPotential (D n) 0 corridor).indicator
              (fun _ => (1 : ℝ)) (field r)) ≤
              (m : ℝ) * pzMean.toReal / 4} ≤
        ENNReal.ofReal (Real.exp (-((m : ℝ) * pzMean.toReal / 4))) := by
    simpa [corridor, spineEvent, lowerMean, upperMean, pairBound, pzMean,
      drift, width, endpointUpper] using hlowCount
  calc
    (finiteRootStepFieldLaw μ m)
      {field : FiniteRootStepField m ℕ ℝ |
        ∀ r : Fin m,
          field r ∉ hasPathHistoryIn (ι := ℕ) realPotential (D n) 0 corridor} ≤
      (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ ℝ |
          (∑ r : Fin m,
            (hasPathHistoryIn (ι := ℕ) realPotential (D n) 0 corridor).indicator
              (fun _ => (1 : ℝ)) (field r)) ≤
              (m : ℝ) * pzMean.toReal / 4} := measure_mono havoidSubset
    _ ≤ ENNReal.ofReal (Real.exp (-((m : ℝ) * pzMean.toReal / 4))) := hlowCount'

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

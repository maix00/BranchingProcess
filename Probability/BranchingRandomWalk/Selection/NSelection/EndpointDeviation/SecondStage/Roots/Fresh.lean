/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.PZ
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily

/-!
# Second-stage failure below predictable roots

At a fixed generation, a measurable injective family of particle addresses
exposes an independent family of fresh descendant fields.  The second-stage
corridor PZ estimate therefore bounds the probability that a past event occurs
and every selected descendant field misses the corridor.  A separate pathwise
argument must still identify the past event with the restarted killed
population.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- The relative affine tube used for a second-stage descendant tree. -/
noncomputable def rightTailPositiveASecondStageCorridor
    (D : ℕ) (κ c v : ℝ) : Set (Fin (D + 1) → ℝ) :=
  affineCorridorThrough D 0
    (rightTailPositiveASecondStageSlope κ c D)
    (rightTailPositiveASecondStageWidth c D)
    (rightTailPositiveASecondStageSlope κ c D * (D : ℝ) +
      v * ((D : ℝ) ^ ((1 : ℝ) / 3)))

/-- All roots fail to produce a path through the second-stage tube. -/
def rightTailPositiveASecondStageFailureEvent
    (m D : ℕ) (κ c v : ℝ) : Set (FiniteRootStepField m ℕ ℝ) :=
  {field | ∀ r : Fin m,
    field r ∉ hasPathHistoryIn (ι := ℕ) realPotential D 0
      (rightTailPositiveASecondStageCorridor D κ c v)}

/-- The explicit one-root PZ ratio for the second-stage tube. -/
noncomputable def rightTailPositiveASecondStagePZMean
    (μ : Measure (Step ℕ ℝ)) (D : ℕ) (κ c v : ℝ) : ℝ≥0∞ := by
  let drift := rightTailPositiveASecondStageSlope κ c D
  let width := rightTailPositiveASecondStageWidth c D
  let endpointUpper := drift * (D : ℝ) + v * ((D : ℝ) ^ ((1 : ℝ) / 3))
  let corridor := rightTailPositiveASecondStageCorridor D κ c v
  let spineEvent : Set (ℕ → ℝ) :=
    {increment | RandomWalk.history D 0 increment ∈ corridor}
  let lowerMean : ℝ≥0∞ := ENNReal.ofReal (Real.exp (0 - 0)) *
    (tiltedIncrementFieldLaw realPotential μ) spineEvent
  let upperMean : ℝ≥0∞ := ENNReal.ofReal (Real.exp (endpointUpper - 0)) *
    (tiltedIncrementFieldLaw realPotential μ) spineEvent
  let pairBound : ℝ≥0∞ := ∑ j : Fin D,
    ENNReal.ofReal (Real.exp (-(2 * 0))) *
      (ENNReal.ofReal (Real.exp (2 * endpointUpper)) * (1 : ℝ≥0∞) ^ 2) *
      (∫⁻ ξ, crossChildWeight realPotential ξ ∂μ) *
      (ENNReal.ofReal (Real.exp (0 - (0 + drift * (j.val : ℝ)))) *
        (tiltedIncrementFieldLaw realPotential μ)
          {increment | RandomWalk.history j.val 0 increment ∈
            affineCorridorPrefix j.val 0 drift width})
  exact lowerMean ^ 2 / (upperMean + pairBound)

/-- A predictable family of same-generation particles has the exact fresh
forest law.  Combined with the finite-variance PZ estimate, the chance that
the past event occurs and all selected descendant trees fail is bounded by the
past-event probability times the independent-root exponential. -/
theorem eventually_measure_predictableSecondStageRoots_allAvoid_le
    {Root : Type*} {m : ℕ}
    [MeasurableSpace (RootIndexed.TreeNode Root ℕ)]
    [Countable (RootIndexed.TreeNode Root ℕ)]
    {D generation : ℕ → ℕ}
    (hD : Tendsto (fun n => (D n : ℝ)) atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hcross : HasFiniteCrossWeight realPotential μ)
    {sigma κ c v : ℝ}
    (hν : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) μ) (sigma ^ 2))
    (hsigma : 0 < sigma) (hκ : 0 ≤ κ) (hc : 0 < c) (hv : 0 < v)
    (hκv : κ / c ^ 2 < v)
    (hterminal : κ / c ^ 2 ≤ 2 * v / 5)
    (hentranceWidth : (5 * (κ / c ^ 2) + v) / 2 ≤ c)
    (hm : 0 < m)
    (chosen : ℕ → RootIndexed.StepField Root ℕ ℝ →
      Fin m → Root × TreeNode ℕ)
    (hcount : ∀ n, (Set.range (chosen n)).Countable)
    (hfiber : ∀ n roots, MeasurableSet[
      RootIndexed.stepFiltration (Root := Root) (α := ℕ) (X := ℝ)
        (generation n)]
      {field | chosen n field = roots})
    (hdepth : ∀ n field i, (chosen n field i).2.length = generation n)
    (hinj : ∀ n field, Function.Injective (chosen n field))
    (A : ℕ → Set (RootIndexed.StepField Root ℕ ℝ))
    (hA : ∀ n, MeasurableSet[
      RootIndexed.stepFiltration (Root := Root) (α := ℕ) (X := ℝ)
        (generation n)] (A n)) :
    ∃ entryQ : ℝ≥0∞, 0 < entryQ ∧
      ∃ C : ℝ, C < 0 ∧ ∃ bridgeQ : ℝ≥0∞, 0 < bridgeQ ∧
        ∃ amplitude : ℝ, 0 < amplitude ∧
          ∀ᶠ n : ℕ in atTop,
            let pzMean := rightTailPositiveASecondStagePZMean
              μ (D n) κ c v
            (RootIndexed.stepFieldLaw (Root := Root) μ)
              (A n ∩
                RootIndexed.selectedSubtreeStepFieldVector (chosen n) ⁻¹'
                  rightTailPositiveASecondStageFailureEvent m (D n) κ c v) ≤
              (RootIndexed.stepFieldLaw (Root := Root) μ) (A n) *
                ENNReal.ofReal (Real.exp (-((m : ℝ) * pzMean.toReal / 4))) := by
  have havoid :=
    eventually_measure_rightTailPositiveASecondStage_allRootsAvoid_le_of_centeredSecondMoment
      (D := D) hD μ hboundary hcross hν hsigma hκ hc hv hκv hterminal
      hentranceWidth m hm
  obtain ⟨entryQ, hentryQ, C, hC, bridgeQ, hbridgeQ, amplitude,
      hamplitude, havoid⟩ := havoid
  refine ⟨entryQ, hentryQ, C, hC, bridgeQ, hbridgeQ, amplitude,
    hamplitude, ?_⟩
  filter_upwards [havoid] with n havoidN
  let corridor := rightTailPositiveASecondStageCorridor (D n) κ c v
  let success := hasPathHistoryIn (ι := ℕ) realPotential (D n) 0 corridor
  let failure := rightTailPositiveASecondStageFailureEvent m (D n) κ c v
  have hcorridor : MeasurableSet corridor := by
    dsimp [corridor, rightTailPositiveASecondStageCorridor]
    exact measurableSet_affineCorridorThrough (D n) 0
      (rightTailPositiveASecondStageSlope κ c (D n))
      (rightTailPositiveASecondStageWidth c (D n))
      (rightTailPositiveASecondStageSlope κ c (D n) * (D n : ℝ) +
        v * ((D n : ℝ) ^ ((1 : ℝ) / 3)))
  have hsuccess : MeasurableSet success :=
    measurableSet_hasPathHistoryIn realPotential (D n) 0 corridor hcorridor
  have hfailure : MeasurableSet failure := by
    rw [show failure = ⋂ r : Fin m,
        (fun field : FiniteRootStepField m ℕ ℝ => field r) ⁻¹' successᶜ by
      ext field
      simp [failure, rightTailPositiveASecondStageFailureEvent,
        success, corridor, rightTailPositiveASecondStageCorridor]]
    apply MeasurableSet.iInter
    intro r
    exact hsuccess.compl.preimage (measurable_pi_apply r)
  have hfactor := RootIndexed.selectedSubtreeStepFieldVector_event_factorization
    μ (chosen n) (hcount n) (hfiber n) (hdepth n) (hinj n)
      (A n) failure (hA n) hfailure
  let pzMean := rightTailPositiveASecondStagePZMean μ (D n) κ c v
  have hfailureBound :
      (finiteRootStepFieldLaw μ m) failure ≤
        ENNReal.ofReal (Real.exp (-((m : ℝ) * pzMean.toReal / 4))) := by
    simpa [failure, pzMean, rightTailPositiveASecondStageFailureEvent,
      rightTailPositiveASecondStagePZMean,
      rightTailPositiveASecondStageCorridor, success, corridor,
      rightTailPositiveASecondStageSlope, rightTailPositiveASecondStageWidth]
      using havoidN
  calc
    (RootIndexed.stepFieldLaw (Root := Root) μ)
        (A n ∩ RootIndexed.selectedSubtreeStepFieldVector (chosen n) ⁻¹'
          rightTailPositiveASecondStageFailureEvent m (D n) κ c v) =
        (RootIndexed.stepFieldLaw (Root := Root) μ) (A n) *
          (finiteRootStepFieldLaw μ m) failure := by
            simpa [failure] using hfactor
    _ ≤ (RootIndexed.stepFieldLaw (Root := Root) μ) (A n) *
        ENNReal.ofReal (Real.exp (-((m : ℝ) * pzMean.toReal / 4))) := by
          gcongr

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

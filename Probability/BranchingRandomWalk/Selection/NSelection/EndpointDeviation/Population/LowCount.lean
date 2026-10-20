/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Population.Embedding
/-!
# First-stage lower count in the killed population

A successful initial root gives a distinct particle in the actual restarted
killed population. This module transfers the independent-root PZ low-count
bound to the population used by the second stage.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- The affine-corridor PZ estimate bounds the probability that the actual
restarted killed population has no more than the independent-root PZ
threshold. The embedding into the actual population holds almost surely by
boundary normalization. -/
theorem measure_rightTailPositiveA_population_le_pzThreshold_le_exp_of_affineCorridorDrawdown
    (m ell ellN : ℕ) (hm : 0 < m) (logN b v c κ : ℝ)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hcross : HasFiniteCrossWeight realPotential μ)
    (q : ℕ → ℝ≥0∞) (hqTop : ∀ n, q n ≠ ∞)
    (hdrawdown : ∀ n,
      (tiltedIncrementFieldLaw realPotential μ)
        (RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          n (b * logN) (b * logN)) ≤ q n)
    (hspinePositive : 0 < (tiltedIncrementFieldLaw realPotential μ)
      {increment | RandomWalk.history ell 0 increment ∈
        affineCorridorThrough ell (-b * logN) 0 (b * logN)
          ((-b + v) * logN)})
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)] :
    let corridor := affineCorridorThrough ell (-b * logN) 0
      (b * logN) ((-b + v) * logN)
    let spineEvent := {increment : ℕ → ℝ |
      RandomWalk.history ell 0 increment ∈ corridor}
    let lowerMean := ENNReal.ofReal (Real.exp (-b * logN)) *
      (tiltedIncrementFieldLaw realPotential μ) spineEvent
    let upperMean := ENNReal.ofReal (Real.exp ((-b + v) * logN)) *
      (tiltedIncrementFieldLaw realPotential μ) spineEvent
    let pairBound := ∑ j : Fin ell,
      ENNReal.ofReal (Real.exp 0) *
        (ENNReal.ofReal (Real.exp (2 * ((-b + v) * logN))) *
          q (ell - j.val - 1) ^ 2) *
        (∫⁻ ξ, crossChildWeight realPotential ξ ∂μ) *
        (ENNReal.ofReal (Real.exp (0 - (-b * logN))) *
          (tiltedIncrementFieldLaw realPotential μ)
            {increment | RandomWalk.history j.val 0 increment ∈
              affineCorridorPrefix j.val (-b * logN) 0 (b * logN)})
    let pzMean := lowerMean ^ 2 / (upperMean + pairBound)
    let initial := RootIndexed.initialPopulation (α := ℕ)
      (Finset.univ : Finset (Fin m))
    let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
    let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
    let populationFinite :=
      RootIndexed.CausalPopulation.ofRestartedRealPositionSets_finiteSlices
        (fun _ : Fin m => 0) id measurable_id initial
        (by simp [initial, RootIndexed.mem_initialPopulation_iff])
        ell window (measurableSet_rightTailPositiveARestartedWindow
          ell ellN logN b v c κ)
        upper (rightTailPositiveARestartedWindow_subset_Iic_upper
          ell ellN logN b v c κ)
    (finiteRootStepFieldLaw μ m)
      {field | ((populationFinite.toFinset ell field).card : ℝ) ≤
        (m : ℝ) * pzMean.toReal / 4} ≤
      ENNReal.ofReal (Real.exp (-((m : ℝ) * pzMean.toReal / 4))) := by
  classical
  let corridor := affineCorridorThrough ell (-b * logN) 0
    (b * logN) ((-b + v) * logN)
  let spineEvent : Set (ℕ → ℝ) :=
    {increment | RandomWalk.history ell 0 increment ∈ corridor}
  let lowerMean : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (-b * logN)) *
      (tiltedIncrementFieldLaw realPotential μ) spineEvent
  let upperMean : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp ((-b + v) * logN)) *
      (tiltedIncrementFieldLaw realPotential μ) spineEvent
  let pairBound : ℝ≥0∞ :=
    ∑ j : Fin ell,
      ENNReal.ofReal (Real.exp 0) *
        (ENNReal.ofReal (Real.exp (2 * ((-b + v) * logN))) *
          q (ell - j.val - 1) ^ 2) *
        (∫⁻ ξ, crossChildWeight realPotential ξ ∂μ) *
        (ENNReal.ofReal (Real.exp (0 - (-b * logN))) *
          (tiltedIncrementFieldLaw realPotential μ)
            {increment | RandomWalk.history j.val 0 increment ∈
              affineCorridorPrefix j.val (-b * logN) 0 (b * logN)})
  let pzMean : ℝ≥0∞ := lowerMean ^ 2 / (upperMean + pairBound)
  let initial := RootIndexed.initialPopulation (α := ℕ)
    (Finset.univ : Finset (Fin m))
  let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
  let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
  let populationFinite :=
    RootIndexed.CausalPopulation.ofRestartedRealPositionSets_finiteSlices
      (fun _ : Fin m => 0) id measurable_id initial
      (by simp [initial, RootIndexed.mem_initialPopulation_iff])
      ell window (measurableSet_rightTailPositiveARestartedWindow
        ell ellN logN b v c κ)
      upper (rightTailPositiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ)
  let successfulRoots : RootIndexed.StepField (Fin m) ℕ ℝ → Finset (Fin m) :=
    fun field => rightTailPositiveASuccessfulRoots m ell logN b v field
  have hbound := measure_rightTailPositiveAFirstStageLowCount_le_of_affineCorridorDrawdown
    m ell hm 0 (-b * logN) 0 (b * logN) ((-b + v) * logN)
    (by norm_num) μ hboundary hcross q hqTop
    (by intro n; simpa using hdrawdown n) hspinePositive
  have hsuccessEmbedding := ae_rightTailPositiveA_successfulRoots_card_le_killedPopulation
    m ell ellN logN b v c κ μ hboundary
  let rootsLow : Set (RootIndexed.StepField (Fin m) ℕ ℝ) :=
    {field | (∑ r : Fin m,
      (hasPathHistoryIn (ι := ℕ) realPotential ell 0 corridor).indicator
        (fun _ => (1 : ℝ)) (field r)) ≤ (m : ℝ) * pzMean.toReal / 4}
  let populationLow : Set (RootIndexed.StepField (Fin m) ℕ ℝ) :=
    {field | ((populationFinite.toFinset ell field).card : ℝ) ≤
      (m : ℝ) * pzMean.toReal / 4}
  have hcountEq (field : RootIndexed.StepField (Fin m) ℕ ℝ) :
      (∑ r : Fin m,
        (hasPathHistoryIn (ι := ℕ) realPotential ell 0 corridor).indicator
          (fun _ => (1 : ℝ)) (field r)) =
        (successfulRoots field).card := by
    simp [successfulRoots, rightTailPositiveASuccessfulRoots, corridor,
      Set.indicator]
  have hsubset : ∀ᵐ field ∂finiteRootStepFieldLaw μ m,
      field ∈ populationLow → field ∈ rootsLow := by
    filter_upwards [hsuccessEmbedding] with field hEmbedding
    intro hpopulation
    change ((populationFinite.toFinset ell field).card : ℝ) ≤
      (m : ℝ) * pzMean.toReal / 4 at hpopulation
    have hcard : (successfulRoots field).card ≤
        (populationFinite.toFinset ell field).card := hEmbedding
    have hcardReal : ((successfulRoots field).card : ℝ) ≤
        ((populationFinite.toFinset ell field).card : ℝ) := by
      exact_mod_cast hcard
    have hrootle : ((successfulRoots field).card : ℝ) ≤
        (m : ℝ) * pzMean.toReal / 4 := hcardReal.trans hpopulation
    change (∑ r : Fin m,
      (hasPathHistoryIn (ι := ℕ) realPotential ell 0 corridor).indicator
        (fun _ => (1 : ℝ)) (field r)) ≤ _
    rw [hcountEq field]
    exact hrootle
  have hrootsBound :
      (finiteRootStepFieldLaw μ m) rootsLow ≤
        ENNReal.ofReal (Real.exp (-((m : ℝ) * pzMean.toReal / 4))) := by
    simpa [rootsLow, corridor, lowerMean, upperMean, pairBound, pzMean,
      spineEvent, RandomWalk.history]
      using hbound
  calc
    (finiteRootStepFieldLaw μ m) populationLow ≤
        (finiteRootStepFieldLaw μ m) rootsLow := measure_mono_ae hsubset
    _ ≤ ENNReal.ofReal (Real.exp (-((m : ℝ) * pzMean.toReal / 4))) := hrootsBound

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity.Spine
import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
import Probability.Process.RandomWalk.Path.Restart.Basic
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Event
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Basic
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Rate.LogScales
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Cutoff
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.SecondStageTube
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Window
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.PairBound

/-!
# Restarted-window probability bound

This module contains the one-use probability comparison required by the
positive-initial-mass capacity proof, Proposition 3.1, equation (4.15), of
Elie Aïdékon and Yueyun Hu, *Average-weight percolation on the complete
graph*, arXiv:2512.23266 (2025). The event definitions and reusable path
inclusions are in `Spine/SecondStageTube.lean`.

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.iidSequenceLaw_restartedWindowProbability_le_secondStageDrawdown` bounds each post-cutoff restarted-window probability by the corresponding finite-prefix drawdown probability.
-/

open Filter MeasureTheory
open scoped ENNReal BigOperators Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- Under an IID increment law, the restarted-window probability after the
cutoff is bounded by the drawdown probability of the shifted second-stage
prefix at its actual length. -/
lemma iidSequenceLaw_restartedWindowProbability_le_secondStageDrawdown
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (ell ellN k : ℕ) (logN b v c κ : ℝ)
    (hk : ell < k) (hkN : k ≤ ellN)
    (hκ : 0 ≤ κ) (hc : 0 < c) (hvc : v ≤ c) :
    RandomWalk.restartedWindowProbability (iidSequenceLaw ν) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ) k 0 ≤
      iidSequenceLaw ν
        (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          (k - ell)
          (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
          (rightTailPositiveADrift ell ellN κ c (k - ell) +
            c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) := by
  let d := k - ell
  let tubePrefix := rightTailPositiveASecondStageTubePrefixEvent ell ellN d κ c v
  let shift : (ℕ → ℝ) → (ℕ → ℝ) := fun increment j => increment (ell + j)
  have hd : d ≤ ellN - ell := by dsimp [d]; omega
  have hDpos : 0 < ellN - ell := by omega
  have hsubsetRestart :
      {increment : ℕ → ℝ |
        InRestartedWindows ell
          (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          (history k 0 increment)} ⊆ shift ⁻¹' tubePrefix := by
    intro increment hmem
    change shift increment ∈ tubePrefix
    simpa [d, tubePrefix, shift] using
      (rightTailPositiveARestartedWindow_event_subset_shiftedSecondStageTubePrefix
        ell ellN k logN b v c κ hk hkN) hmem
  have hsubsetDrawdown : tubePrefix ⊆
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        d
        (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
        (rightTailPositiveADrift ell ellN κ c d +
          c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) :=
    rightTailPositiveASecondStageTubePrefixEvent_subset_drawdownEvent
      ell ellN d κ c v (lt_of_lt_of_le hk hkN) hd hκ hc hvc
  have hprefixMeas : MeasurableSet tubePrefix := by
    classical
    rw [show tubePrefix = ⋂ j : Fin (d + 1),
        {increment : ℕ → ℝ |
          AdditivePath.displacement (j : ℕ) increment ∈
            rightTailPositiveASecondStageWindow ell ellN κ c v (j : ℕ)} by
      ext increment
      simp [tubePrefix, rightTailPositiveASecondStageTubePrefixEvent]]
    apply MeasurableSet.iInter
    intro j
    have hwindow : MeasurableSet
        (rightTailPositiveASecondStageWindow ell ellN κ c v (j : ℕ)) := by
      dsimp [rightTailPositiveASecondStageWindow]
      split_ifs <;> simp [measurableSet_Icc]
    exact hwindow.preimage (displacement_measurable (j : ℕ))
  have hshiftMeas : Measurable shift := measurable_natAdd ell
  have hshiftLaw : (iidSequenceLaw ν).map shift = iidSequenceLaw ν := by
    simpa [shift] using iidSequenceLaw_map_natAdd ν ell
  unfold RandomWalk.restartedWindowProbability
  change (iidSequenceLaw ν)
      {increment : ℕ → ℝ |
        InRestartedWindows ell
          (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          (history k 0 increment)} ≤ _
  calc
    _ ≤ (iidSequenceLaw ν) (shift ⁻¹' tubePrefix) := measure_mono hsubsetRestart
    _ = (iidSequenceLaw ν).map shift tubePrefix := by
      rw [Measure.map_apply hshiftMeas hprefixMeas]
    _ = (iidSequenceLaw ν) tubePrefix := by rw [hshiftLaw]
    _ ≤ (iidSequenceLaw ν)
        (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          d
          (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
          (rightTailPositiveADrift ell ellN κ c d +
            c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) :=
      measure_mono hsubsetDrawdown

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

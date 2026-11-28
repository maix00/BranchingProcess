/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity.Spine
import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
import Probability.Process.RandomWalk.Path.Restart.Basic
import Probability.Process.Path.Restart.Basic
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.LogarithmicScales
import LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.FirstStage.Cutoff
import all LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.SecondStage.Capacity.Lemmas.Tube.Event
import LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.Population.RestartedWindow
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.PairBound

/-!
# Probability of a shifted second-stage prefix

## Internal proof declarations

* `iidSequenceLaw_restartedWindowProbability_le_secondStagePrefix` gives
  $\mathbb P(W_k)\le\mathbb P(T_{k-\ell})$, where $W_k$ is the restarted
  window event through time $k$ and $T_{k-\ell}$ is its relative tube prefix.

The comparison uses shift invariance of the increment law in the
two-stage construction of Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (Fudan University, 2026), Chapter 4,
Theorem 1.1, case $0<a<1$.
-/

open Filter MeasureTheory
open scoped ENNReal BigOperators Topology

namespace LiteratureProofTest.Wang2026AsymptoticSpeed

open ProbabilityTheory

open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
open Asymptotics

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.Process.Path

/-- Under an IID increment law, the restarted-window probability after the
cutoff is bounded by the probability of the shifted second-stage prefix. -/
lemma iidSequenceLaw_restartedWindowProbability_le_secondStagePrefix
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (ell ellN k : ℕ) (logN b v c κ : ℝ)
    (hk : ell < k) (hkN : k ≤ ellN) :
    ProbabilityTheory.RandomWalk.restartedWindowProbability (iidSequenceLaw ν) ell
        (positiveARestartedWindow ell ellN logN b v c κ) k 0 ≤
      iidSequenceLaw ν (positiveASecondStageTubePrefixEvent ell ellN (k - ell) κ c v) := by
  let d := k - ell
  let tubePrefix := positiveASecondStageTubePrefixEvent ell ellN d κ c v
  let shift : (ℕ → ℝ) → (ℕ → ℝ) := fun increment j => increment (ell + j)
  have hsubsetRestart :
      {increment : ℕ → ℝ |
        InRestartedWindows ell
          (positiveARestartedWindow ell ellN logN b v c κ)
          (history k 0 increment)} ⊆ shift ⁻¹' tubePrefix := by
    intro increment hmem
    change shift increment ∈ tubePrefix
    simpa [d, tubePrefix, shift] using
      (positiveARestartedWindow_event_subset_shiftedSecondStageTubePrefix
        ell ellN k logN b v c κ hk hkN) hmem
  have hprefixMeas : MeasurableSet tubePrefix := by
    classical
    rw [show tubePrefix = ⋂ j : Fin (d + 1),
        {increment : ℕ → ℝ |
          AdditivePath.displacement (j : ℕ) increment ∈
            positiveASecondStageWindow ell ellN κ c v (j : ℕ)} by
      ext increment
      simp [tubePrefix, positiveASecondStageTubePrefixEvent]]
    apply MeasurableSet.iInter
    intro j
    have hwindow : MeasurableSet
        (positiveASecondStageWindow ell ellN κ c v (j : ℕ)) := by
      dsimp [positiveASecondStageWindow]
      split_ifs <;> simp [measurableSet_Icc]
    exact hwindow.preimage (displacement_measurable (j : ℕ))
  have hshiftMeas : Measurable shift := measurable_natAdd ell
  have hshiftLaw : (iidSequenceLaw ν).map shift = iidSequenceLaw ν := by
    simpa [shift] using iidSequenceLaw_map_natAdd ν ell
  unfold ProbabilityTheory.RandomWalk.restartedWindowProbability
  change (iidSequenceLaw ν)
      {increment : ℕ → ℝ |
        InRestartedWindows ell
          (positiveARestartedWindow ell ellN logN b v c κ)
          (history k 0 increment)} ≤ _
  calc
    _ ≤ (iidSequenceLaw ν) (shift ⁻¹' tubePrefix) := measure_mono hsubsetRestart
    _ = (iidSequenceLaw ν).map shift tubePrefix := by
      rw [Measure.map_apply hshiftMeas hprefixMeas]
    _ = (iidSequenceLaw ν) tubePrefix := by rw [hshiftLaw]

end LiteratureProofTest.Wang2026AsymptoticSpeed

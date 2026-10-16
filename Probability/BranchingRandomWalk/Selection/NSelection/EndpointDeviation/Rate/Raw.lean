/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Basic
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Basic

/-!
# Finite-horizon selected-population endpoint decomposition

The spine increment field is the i.i.d. sequence law of the tilted one-step
potential law. The public theorem gives the finite-horizon branching endpoint
bound for any supplied i.i.d. spine estimate:

`P(selected endpoint ≤ r) ≤ N(H+1)² exp(-B) + m exp(r) P(no drop > B, Y_H ≤ r)`.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown
open ProbabilityTheory.BranchingRandomWalk.Spine

private lemma history_coordinate_eq_displacement (n : ℕ)
    (increment : ℕ → ℝ) (i : Fin (n + 1)) :
    ProbabilityTheory.RandomWalk.history n 0 increment i =
      AdditivePath.displacement i.val increment := by
  rw [ProbabilityTheory.RandomWalk.history_eq_fromIncrements]
  simp [AdditivePath.fromIncrements, AdditivePath.displacement]

/-- The spine's finite-history definition agrees with the natural-time
drawdown event used by the block estimate. -/
private lemma spineNoLargeDropEndpointBelowEvent_eq_randomWalkEvent
    (n : ℕ) (delta threshold : ℝ) :
    spineNoLargeDropEndpointBelowEvent n delta threshold =
      noLargeDropEndpointBelowEvent n delta threshold := by
  ext increment
  change ProbabilityTheory.RandomWalk.historyNoLargeDropAndEndpointBelow
      delta threshold (ProbabilityTheory.RandomWalk.history n 0 increment) ↔
    (∀ i j : ℕ, i ≤ j → j ≤ n →
      AdditivePath.displacement i increment -
        AdditivePath.displacement j increment ≤ delta) ∧
      AdditivePath.displacement n increment ≤ threshold
  constructor
  · rintro ⟨hdrop, hendpoint⟩
    refine ⟨?_, ?_⟩
    · intro i j hij hj
      let i' : Fin (n + 1) := ⟨i, by omega⟩
      let j' : Fin (n + 1) := ⟨j, by omega⟩
      have h := hdrop i' j' (by simp [i', j', hij])
      simpa [i', j', history_coordinate_eq_displacement] using h
    · simpa [ProbabilityTheory.RandomWalk.history_last,
        AdditivePath.fromIncrements, AdditivePath.displacement] using hendpoint
  · rintro ⟨hdrop, hendpoint⟩
    refine ⟨?_, ?_⟩
    · intro i j hij
      have h := hdrop i.val j.val hij (by omega)
      simpa [history_coordinate_eq_displacement] using h
    · simpa [ProbabilityTheory.RandomWalk.history_last,
        AdditivePath.fromIncrements, AdditivePath.displacement] using hendpoint

/-- The finite-horizon endpoint decomposition with its no-large-drawdown
term bounded by any supplied i.i.d. spine estimate. -/
theorem measure_firstNSelectedEndpointBelow_le_of_iidSpineBound
    (m N H : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hmN : m ≤ N) (B threshold : ℝ) (hB : 0 < B)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    (bound : ℝ≥0∞)
    (hwalk : iidSequenceLaw ν
        (noLargeDropEndpointBelowEvent H B threshold) ≤ bound) :
    (finiteRootStepFieldLaw μ m)
        (firstNSelectedEndpointBelow m N H threshold) ≤
      (N : ℝ≥0∞) *
          (((H : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B))) +
        (m : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp threshold) * bound) := by
  have hspine : (tiltedIncrementFieldLaw realPotential μ)
      (spineNoLargeDropEndpointBelowEvent H B threshold) ≤ bound := by
    rw [show tiltedIncrementFieldLaw realPotential μ = iidSequenceLaw ν by
      rw [hν]
      rfl,
      spineNoLargeDropEndpointBelowEvent_eq_randomWalkEvent]
    exact hwalk
  have hdecomp := measure_firstNSelectedEndpointBelow_le_of_drawdown
    m N H hmN B threshold hB μ hboundary
  calc
    (finiteRootStepFieldLaw μ m)
        (firstNSelectedEndpointBelow m N H threshold) ≤
      (N : ℝ≥0∞) *
          (((H : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B))) +
        (m : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp threshold) *
            (tiltedIncrementFieldLaw realPotential μ)
              (spineNoLargeDropEndpointBelowEvent H B threshold)) := hdecomp
    _ ≤ (N : ℝ≥0∞) *
          (((H : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B))) +
        (m : ℝ≥0∞) * (ENNReal.ofReal (Real.exp threshold) * bound) := by
      have htail :
          (m : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp threshold) *
                (tiltedIncrementFieldLaw realPotential μ)
                  (spineNoLargeDropEndpointBelowEvent H B threshold)) ≤
            (m : ℝ≥0∞) * (ENNReal.ofReal (Real.exp threshold) * bound) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hspine (by positivity)) (by positivity)
      simpa [add_comm] using add_le_add_left htail
        ((N : ℝ≥0∞) * (((H : ℝ≥0∞) + 1) ^ 2 *
          ENNReal.ofReal (Real.exp (-B))))

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

end

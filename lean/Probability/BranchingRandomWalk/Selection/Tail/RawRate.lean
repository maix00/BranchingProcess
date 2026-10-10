/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.Tail.Endpoint
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.RawRangeRate

/-!
# Raw random-walk rates in the selected-population endpoint estimate

The spine increment field is the i.i.d. sequence law of the tilted one-step
potential law.  This module substitutes the raw increment-law Mogul'skii
estimate into the existing finite-horizon branching endpoint decomposition.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown
open ProbabilityTheory.BranchingRandomWalk.Spine

private theorem history_coordinate_eq_displacement (n : ℕ)
    (increment : ℕ → ℝ) (i : Fin (n + 1)) :
    ProbabilityTheory.RandomWalk.history n 0 increment i =
      AdditivePath.displacement i.val increment := by
  rw [ProbabilityTheory.RandomWalk.history_eq_fromIncrements]
  simp [AdditivePath.fromIncrements, AdditivePath.displacement]

/-- The spine's finite-history definition agrees with the natural-time
drawdown event used by the block estimate. -/
private theorem spineNoLargeDropEndpointBelowEvent_eq_randomWalkEvent
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

/-- The branching endpoint estimate with the raw finite-variance range rate
substituted for the spine probability.  All sequence-scale hypotheses are
explicit, so this is the analytic input for specializing to
`H_N ~ log^3 N` and `B_N ~ log N`. -/
theorem eventually_finiteRootStepFieldLaw_firstNSelectedEndpointBelow_le_of_rangeRate
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    {sigma : ℝ}
    (hspineMoment : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) μ) (sigma ^ 2))
    (hsigma : 0 < sigma)
    {scale : ℕ → ℝ}
    (hscale : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    {m N horizon blocks length : ℕ → ℕ}
    (horder : ∀ n, LinearOrder (RootIndexed.TreeNode (Fin (m n)) ℕ))
    {delta width threshold : ℕ → ℝ} (K k : ℕ)
    {factor eta rangeRate targetRate : ℝ}
    (hfactor : 1 < factor) (heta : 0 < eta)
    (hrangeRate : 0 < rangeRate) (hk : 0 < k)
    (hrangeRate_lt : rangeRate < (Real.pi ^ 2 / 2) *
      (rangeCoverUnion k hk).realEnergy)
    (htargetRate : 0 < targetRate)
    (hlength : Tendsto (fun n => length n + 1) atTop atTop)
    (hblocks : Tendsto blocks atTop atTop)
    (hblockCost : Tendsto
      (fun n => ((length n + 1 : ℕ) : ℝ) / delta n ^ 2) atTop atTop)
    (htotalCost : Tendsto
      (fun n => (horizon n : ℝ) / delta n ^ 2) atTop atTop)
    (hcovered : Tendsto
      (fun n => (blocks n : ℝ) *
        (((length n + 1 : ℕ) : ℝ) / delta n ^ 2) /
          ((horizon n : ℝ) / delta n ^ 2)) atTop (𝓝 1))
    (hcomplete : ∀ᶠ n : ℕ in atTop,
      blocks n * length n ≤ horizon n)
    (hwidth : ∀ᶠ n : ℕ in atTop, width n = eta * delta n)
    (hthreshold : ∀ᶠ n : ℕ in atTop,
      ⌊(threshold n + delta n) / width n⌋₊ = K)
    (hscaleBlock : ∀ᶠ n : ℕ in atTop,
      scale (length n + 1) = (factor * (1 + eta) / 2) * delta n)
    (hgap : targetRate < rangeRate / (factor * (1 + eta) / 2) ^ 2)
    (hmN : ∀ᶠ n : ℕ in atTop, m n ≤ N n)
    (hB : ∀ᶠ n : ℕ in atTop, 0 < delta n) :
    ∀ᶠ n : ℕ in atTop,
      (finiteRootStepFieldLaw μ (m n))
        (@firstNSelectedEndpointBelow (m n) (N n) (horizon n) (horder n)
          (threshold n)) ≤
      (N n : ℝ≥0∞) *
          (((horizon n : ℝ≥0∞) + 1) ^ 2 *
            ENNReal.ofReal (Real.exp (-delta n))) +
        (m n : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp (threshold n)) *
            ENNReal.ofReal (Real.exp
              (-targetRate * sigma ^ 2 *
                ((horizon n : ℝ) / delta n ^ 2)))) := by
  let ν : Measure ℝ := tiltedPotentialLaw realPotential (-1) μ
  have hν : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact tiltedPotentialLaw_isProbability realPotential μ hboundary
  letI := hν
  have hspineMoment' : IsCenteredSecondMoment ν (sigma ^ 2) := by
    simpa [ν] using hspineMoment
  have hwalk :=
    eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_of_rangeRate_of_centeredSecondMoment
      ν hspineMoment' hsigma hscale
      (horizon := horizon) (blocks := blocks) (length := length)
      (delta := delta) (width := width) (threshold := threshold)
      K k hfactor heta hrangeRate hk hrangeRate_lt htargetRate hlength hblocks
      hblockCost htotalCost hcovered hcomplete hwidth hthreshold hscaleBlock hgap
  filter_upwards [hwalk, hmN, hB] with n hwalkn hmNn hBn
  letI : LinearOrder (RootIndexed.TreeNode (Fin (m n)) ℕ) := horder n
  have hendpoint := measure_firstNSelectedEndpointBelow_le_of_iidSpineBound
    (m n) (N n) (horizon n) hmNn (delta n) (threshold n) hBn μ hboundary
    ν rfl (ENNReal.ofReal (Real.exp
      (-targetRate * sigma ^ 2 * ((horizon n : ℝ) / delta n ^ 2)))) hwalkn
  simpa [ν] using hendpoint

end ProbabilityTheory.BranchingRandomWalk.Selection.Tail

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Corridor
/-!
# First-stage Paley–Zygmund inputs

Finite variance gives the quantitative tilted-spine corridor mass. For the
MRCA pair bound, the first-stage proof only needs the trivial drawdown bound
by one, so this interface adds no Brownian realization hypothesis.
-/

section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- The finite-variance corridor lower bound and the trivial finite-valued
drawdown bound are available together for every sufficiently large
right-tail first-stage cutoff. These are the random-walk inputs to the
existing MRCA/PZ estimate; neither spine positivity nor a free drawdown
sequence is an assumption. -/
theorem eventually_rightTailPositiveA_firstStagePZInputs_of_centeredSecondMoment
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Combinatorics.Branching.Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma b v : ℝ}
    (hνMoment : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) (hb : 0 < b) (hv : 0 < v) (hvb : v < b)
    :
    ∃ C : ℝ, C < 0 ∧ ∃ entranceMass : ℝ≥0∞, 0 < entranceMass ∧
      ∃ amplitude : ℝ, 0 < amplitude ∧
      ∀ᶠ n : ℕ in atTop,
        rightTailPositiveASpineCorridorLowerBound ν b v C amplitude
            entranceMass (rightTailFirstStageCutoff N n) ≤
          (tiltedIncrementFieldLaw realPotential μ)
            {increment : ℕ → ℝ |
              RandomWalk.history (rightTailFirstStageCutoff N n) 0
                increment ∈
                affineCorridorThrough (rightTailFirstStageCutoff N n)
                  (-b * logarithmOfSampleSize N n) 0
                  (b * logarithmOfSampleSize N n)
                  ((-b + v) * logarithmOfSampleSize N n)} ∧
        0 < (tiltedIncrementFieldLaw realPotential μ)
          {increment : ℕ → ℝ |
            RandomWalk.history (rightTailFirstStageCutoff N n) 0
              increment ∈
              affineCorridorThrough (rightTailFirstStageCutoff N n)
                (-b * logarithmOfSampleSize N n) 0
                (b * logarithmOfSampleSize N n)
                ((-b + v) * logarithmOfSampleSize N n)} ∧
        (∀ k : ℕ,
          (tiltedIncrementFieldLaw realPotential μ)
            (noLargeDropEndpointBelowEvent k
              (b * logarithmOfSampleSize N n)
              (b * logarithmOfSampleSize N n)) ≤ 1) := by
  obtain ⟨C, hC, entranceMass, hentranceMass, amplitude, hamplitude,
      hlower⟩ :=
    eventually_rightTailPositiveA_spineCorridor_lowerBound_of_centeredSecondMoment
      hN μ ν hν hνMoment hsigma hb hv hvb
  have hpositive :=
    eventually_rightTailPositiveA_spineCorridor_pos_of_centeredSecondMoment
      hN μ ν hν hνMoment hsigma hb hv hvb
  have hlaw : tiltedIncrementFieldLaw realPotential μ = iidSequenceLaw ν := by
    rw [hν]
    rfl
  refine ⟨C, hC, entranceMass, hentranceMass, amplitude, hamplitude, ?_⟩
  filter_upwards [hlower, hpositive] with n hnLower hnPositive
  refine ⟨hnLower, hnPositive, ?_⟩
  intro k
  rw [hlaw]
  calc
    (iidSequenceLaw ν)
        (noLargeDropEndpointBelowEvent k
          (b * logarithmOfSampleSize N n)
          (b * logarithmOfSampleSize N n)) ≤
      iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

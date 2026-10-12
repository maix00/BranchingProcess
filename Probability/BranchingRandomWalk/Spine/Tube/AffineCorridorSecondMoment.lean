/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Spine.Tube.AffineCorridorPairBound

/-!
# Second moments in affine corridors

The second moment of a zero-one corridor count is its first moment plus the
sum of the expected ordered path pairs, grouped by the generation of their
most recent common ancestor.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.RandomWalk

/-- The second moment of the generation-`N` affine-corridor count is its
first moment plus the sum of the actual MRCA pair contributions. The
ancestor prefix and the birth-generation corridor condition are retained in
each contribution. -/
theorem lintegral_pathGeneration_affineCorridor_sq_eq_firstMoment_add_mrcaContributions
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (N : ℕ) (initial lower drift width endpointUpper : ℝ) :
    (∫⁻ ω, (pathGeneration φ N
      ((affineCorridorThrough N lower drift width endpointUpper).indicator
        (fun _ => (1 : ℝ≥0∞))) initial ω) ^ 2 ∂stepFieldLaw μ) =
      (∫⁻ ω, pathGeneration φ N
        ((affineCorridorThrough N lower drift width endpointUpper).indicator
          (fun _ => (1 : ℝ≥0∞))) initial ω ∂stepFieldLaw μ) +
        ∑ m : Fin N,
          affineTubeMRCAPairContribution φ μ m.val (N - m.val - 1)
            initial lower drift width endpointUpper := by
  let corridor := affineCorridorThrough N lower drift width endpointUpper
  let F : (Fin (N + 1) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  have hcorridor : MeasurableSet corridor :=
    measurableSet_affineCorridorThrough N lower drift width endpointUpper
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hF01 : ∀ history, F history = 0 ∨ F history = 1 := by
    intro history
    by_cases hhistory : history ∈ corridor <;> simp [F, hhistory]
  have hsecond :=
    lintegral_pathGeneration_sq_eq_add_distinctAddressPairCount
      φ μ N F hF hF01 initial
  have hpair :=
    lintegral_pathGenerationDistinctAddressPairCount_affineCorridor_eq_sum_MRCA
      φ μ hboundary N initial lower drift width endpointUpper
  calc
    _ = (∫⁻ ω, pathGeneration φ N F initial ω ∂stepFieldLaw μ) +
          (∫⁻ ω, pathGenerationDistinctAddressPairCount φ N F initial ω
            ∂stepFieldLaw μ) := hsecond
    _ = (∫⁻ ω, pathGeneration φ N F initial ω ∂stepFieldLaw μ) +
          ∑ m : Fin N,
            affineTubeMRCAPairContribution φ μ m.val (N - m.val - 1)
              initial lower drift width endpointUpper := by
        rw [show (∫⁻ ω, pathGenerationDistinctAddressPairCount φ N F initial ω
            ∂stepFieldLaw μ) =
            ∑ m : Fin N,
              affineTubeMRCAPairContribution φ μ m.val (N - m.val - 1)
                initial lower drift width endpointUpper by
          simpa [F, corridor] using hpair]
    _ = _ := by simp [F, corridor]

end ProbabilityTheory.BranchingRandomWalk.Spine

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Tube.Corridor.PairBound

/-!
# Second moments in affine corridors

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_pathGeneration_affineCorridor_sq_eq_firstMoment_add_mrcaContributions`
  states the exact identity `E[X_N²] = E[X_N] + ∑ m : Fin N, C_m`
  for any probability offspring law, without boundary normalization, where
  `X_N` is the path-generation count restricted to the affine corridor and
  `C_m` is the expected ordered-pair contribution with MRCA generation `m`.

The second moment of a zero-one corridor count is its first moment plus the
sum of the expected ordered path pairs, grouped by the generation of their
most recent common ancestor.

This is the second-moment decomposition used in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(master's thesis, Fudan University, 2026), Chapter 3, Lemma 3.6,
equation (3.7).

Writing \(P_{\mathrm{off}}=\operatorname{offspringFieldLaw}(\mu)\),
\(X_N\) for the number of generation-\(N\) paths in the affine corridor, and
\(C_{m,n}\) for the ordered pair contribution with common ancestor generation
\(m\) and \(n+1\) generations remaining, the identity is
\[
 \int^- X_N^2\,dP_{\mathrm{off}}
 =\int^- X_N\,dP_{\mathrm{off}}
   +\sum_{m=0}^{N-1}C_{m,N-m-1}.
\]
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.RandomWalk

/-- The actual corridor count satisfies the MRCA square decomposition in
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), Chapter 3, Lemma 3.6, equation (3.7).
The pathwise zero-one identity and branching property suffice; boundary
normalization and finiteness of the first moment are not required. -/
theorem lintegral_pathGeneration_affineCorridor_sq_eq_firstMoment_add_mrcaContributions
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (N : ℕ) (initial lower drift width endpointUpper : ℝ) :
    (∫⁻ ω, (pathGeneration φ N
      ((affineCorridorThrough N lower drift width endpointUpper).indicator
        (fun _ => (1 : ℝ≥0∞))) initial ω) ^ 2 ∂offspringFieldLaw μ) =
      (∫⁻ ω, pathGeneration φ N
        ((affineCorridorThrough N lower drift width endpointUpper).indicator
          (fun _ => (1 : ℝ≥0∞))) initial ω ∂offspringFieldLaw μ) +
        ∑ m : Fin N,
          affineTubeMRCAPairContribution φ μ m.val (N - m.val - 1)
            initial lower drift width endpointUpper := by
  let corridor := affineCorridorThrough N lower drift width endpointUpper
  let F := corridor.indicator (fun _ => (1 : ℝ≥0∞))
  have hF : Measurable F := measurable_const.indicator
    (measurableSet_affineCorridorThrough N lower drift width endpointUpper)
  have hmeas (m : Fin N) : Measurable
      (pathGenerationMRCAContribution φ m.val N F initial) := by
    have hN : (N - m.val - 1 + 1) + m.val = N := by omega
    have h := pathGenerationMRCAContribution_affineCorridor_measurable
      φ m.val (N - m.val - 1) initial lower drift width endpointUpper
    rw [hN] at h
    exact h
  calc
    _ = ∫⁻ ω, pathGeneration φ N F initial ω +
        ∑ m : Fin N, pathGenerationMRCAContribution φ m.val N F initial ω
        ∂offspringFieldLaw μ := by
      apply lintegral_congr
      intro ω
      exact pathGeneration_indicator_sq_eq_self_add_sum_mrcaContribution
        φ N corridor initial ω
    _ = (∫⁻ ω, pathGeneration φ N F initial ω ∂offspringFieldLaw μ) +
        ∑ m : Fin N, ∫⁻ ω, pathGenerationMRCAContribution φ m.val N F initial ω
          ∂offspringFieldLaw μ := by
      rw [lintegral_add_left (pathGeneration_measurable φ N hF initial)]
      congr 1
      exact lintegral_finsetSum' Finset.univ (fun m _ => (hmeas m).aemeasurable)
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      have hN : (N - m.val - 1 + 1) + m.val = N := by omega
      have h := lintegral_pathGenerationMRCAContribution_affineCorridor_eq
        φ μ m.val (N - m.val - 1) initial lower drift width endpointUpper
      rw [hN] at h
      exact h

end ProbabilityTheory.BranchingRandomWalk.Spine

end

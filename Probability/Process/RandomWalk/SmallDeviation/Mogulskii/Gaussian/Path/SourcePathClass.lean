/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Gaussian.EscapeConstant
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.Source.PathClassRegimes
/-!
# Explicit Gaussian rate for the source path convention

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Path.tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_source_index_two_of_brownian_explicit`:
  for a normal-domain random walk and a path class with energy $H_2(G)$,
  the source-terminal-left path probability has logarithmic rate
  $-pi^2 H_2(G)/2$ under the exponent-two stable rate normalization.

The Rademacher spectral rate identifies the Brownian escape constant, and the
source endpoint adapter supplies the matching path-class theorem for all
zero-centered normal-domain increment laws, including infinite-variance laws.

This is the source-path form of Theorem 3, Section 4, p. 764 of A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Path

open Skorokhod.PathClass.StepCorridor
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- The source-terminal-left path-class theorem in the normal domain, with the
Brownian escape constant and full-width coefficient evaluated explicitly.
The Brownian input only needs the almost-sure path regularity provided by
Mathlib's `IsBrownianReal`. This is the source-path form of Theorem 3,
Section 4, p. 764 of A. A. Mogul'skii, *Small Deviations in a Space of
Trajectories* (DOI 10.1137/1119081). -/
theorem tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_source_index_two_of_brownian_explicit
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale 2 ν normalization scale)
    (hDOA : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization (fun _ => 0))
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B Q)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation 2 G)
    (hGmeas : MeasurableSet G) :
    HasStableProcessEscapeRate 2 (gaussianReal 0 1)
        (hB.isStableLevyProcess.unitIntervalPathLaw :
          Measure (CadlagPath unitInterval ℝ)) (-(Real.pi ^ 2) / 8) ∧
      (∀ n : ℕ,
        NullMeasurableSet
          {increment : ℕ → ℝ |
            RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}
          (iidSequenceLaw ν)) ∧
      ∃! H : ℝ,
        (∃ A : FiniteCorridorUnionApproximation 2 G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
          H = hLimits.commonEnergy) ∧
        Tendsto
          (fun n : ℕ => Real.log
            ((iidSequenceLaw ν {increment : ℕ → ℝ |
              RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
              stableRateNormalization 2 ν scale n)
          atTop (𝓝 (-(Real.pi ^ 2) / 2 * H)) := by
  rcases tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_source_index_two
      hscale hB.isStableLevyProcess hDOA hG hGmeas with
    ⟨C, hEscape, hNull, H, hH, hUnique⟩
  have hX := hB.isStableLevyProcess
  have hC := HasStableProcessEscapeRate.eq_neg_pi_sq_div_eight
    hEscape hX canonicalMogulskiiScale
  have hfull := HasStableProcessEscapeRate.fullWidthCoefficient_eq_neg_pi_sq_div_two
    hEscape hX canonicalMogulskiiScale
  refine ⟨?_, hNull, H, ⟨hH.1, ?_⟩, ?_⟩
  · simpa [hC] using hEscape
  · have hrate := hH.2
    rw [hfull] at hrate
    exact hrate
  · intro H' hH'
    apply hUnique H'
    refine ⟨hH'.1, ?_⟩
    have hrate := hH'.2
    rw [← hfull] at hrate
    exact hrate

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Path

end

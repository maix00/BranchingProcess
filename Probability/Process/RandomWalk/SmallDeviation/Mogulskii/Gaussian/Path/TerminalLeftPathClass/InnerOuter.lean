/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Gaussian.EscapeConstant
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Lemmas.CanonicalScale
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.TerminalLeft.PathClass.InnerOuter
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.TerminalLeft.PathClass.Rate
import Probability.Distributions.Stable.Attraction.Normal.TruncatedMoment
import Probability.Process.Stable.PathLaw.UnitInterval
import Probability.Process.Stable.Brownian.PathLaw

/-!
# Explicit Gaussian terminal-left inner and outer rates

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Path.existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_source_index_two_of_brownian_explicit`:
  the inner and outer terminal-left path probabilities have the same unique
  exponent-two logarithmic rate, $-\frac{\pi^2}{2}H_2(M)$, for each path class $M$
  with a vanishing-energy-gap approximation.

The source-aligned inner/outer theorem applies in the normal domain of
attraction, including infinite-variance increment laws. The Brownian escape
constant identifies its explicit full-width coefficient as
$-\frac{\pi^2}{2}$.

The rate is the terminal-left path form of Theorem 3, Section 4, p. 764 of A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Path

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- In the normal domain of attraction, source-terminal-left random-walk
paths have the same unique inner and outer logarithmic rate for every path
class `M`. The Brownian escape constant is evaluated explicitly, giving the
full-width coefficient `-π² / 2`. No measurability assumption on the target is
needed, and the normal-domain input allows infinite variance. This is the
terminal-left path form of Theorem 3, Section 4, p. 764 of A. A. Mogul'skii,
*Small Deviations in a Space of Trajectories* (DOI 10.1137/1119081). -/
theorem existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_source_index_two_of_brownian_explicit
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale 2 ν normalization scale)
    (hDOA : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization (fun _ => 0))
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B Q)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation 2 G) :
    HasStableProcessEscapeRate 2 (gaussianReal 0 1)
        (hB.isStableLevyProcess.unitIntervalPathLaw :
          Measure (CadlagPath unitInterval ℝ)) (-(Real.pi ^ 2) / 8) ∧
      ∃! H : ℝ,
        ∃ A : FiniteCorridorUnionApproximation 2 G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
        H = hLimits.commonEnergy ∧
        (∀ᶠ n : ℕ in atTop,
          0 < ((iidSequenceLaw ν).innerMeasure
            {increment : ℕ → ℝ |
              RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
        (∀ᶠ n : ℕ in atTop,
          0 < (iidSequenceLaw ν
            {increment : ℕ → ℝ |
              RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) ∧
        0 < H ∧ H ≤ FiniteCorridorUnion.realEnergy (A.inner 0) ∧
        Tendsto
          (fun n : ℕ => Real.log
            (((iidSequenceLaw ν).innerMeasure
              {increment : ℕ → ℝ |
                RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
                stableRateNormalization 2 ν scale n)
          atTop (𝓝 (-(Real.pi ^ 2) / 2 * H)) ∧
        Tendsto
          (fun n : ℕ => Real.log
            ((iidSequenceLaw ν
              {increment : ℕ → ℝ |
                RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
                stableRateNormalization 2 ν scale n)
          atTop (𝓝 (-(Real.pi ^ 2) / 2 * H)) := by
  let hX := hB.isStableLevyProcess
  have hslow := hDOA.stableSlowVariation_two_isSlowlyVarying_of_gaussian
  have hresult := existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_source_index_two
    hscale hX hDOA hG
  rcases hresult with ⟨C, hEscape, H, hH, hUnique⟩
  rcases hH with ⟨A, hLimits, hEnergyEq, hInnerPos, hOuterPos,
    hPositive, hEnergyUpper, hInnerRate, hOuterRate⟩
  have hC : C = -(Real.pi ^ 2) / 8 :=
    HasStableProcessEscapeRate.eq_neg_pi_sq_div_eight
      hEscape hX canonicalMogulskiiScale
  have hfull : C * 2 ^ (2 : ℝ) = -(Real.pi ^ 2) / 2 :=
    HasStableProcessEscapeRate.fullWidthCoefficient_eq_neg_pi_sq_div_two
      hEscape hX canonicalMogulskiiScale
  have hratePos := stableSmallDeviationRate_pos_eventually hscale hslow
  have hInnerStable :=
    tendsto_log_div_stableRateNormalization_of_neg hratePos hInnerRate
  have hOuterStable :=
    tendsto_log_div_stableRateNormalization_of_neg hratePos hOuterRate
  have hcoef : -(rateCoefficient 2 C * H) = -(Real.pi ^ 2) / 2 * H := by
    rw [rateCoefficient, hfull]
    ring
  refine ⟨?_, H, ⟨A, hLimits, hEnergyEq, hInnerPos, hOuterPos,
    hPositive, hEnergyUpper, ?_, ?_⟩, ?_⟩
  · simpa [hC] using hEscape
  · simpa [hcoef] using hInnerStable
  · simpa [hcoef] using hOuterStable
  · intro H' hH'
    obtain ⟨A', hLimits', hEnergyEq', hInnerPos', hOuterPos',
      hPositive', hEnergyUpper', hInnerStable', hOuterStable'⟩ := hH'
    have hInnerRate' :=
      tendsto_log_div_probabilityRateDenominator_of_stableRateNormalization
        hratePos hInnerStable'
    have hOuterRate' :=
      tendsto_log_div_probabilityRateDenominator_of_stableRateNormalization
        hratePos hOuterStable'
    have hcoef' : rateCoefficient 2 C * H' =
        - (-(Real.pi ^ 2) / 2 * H') := by
      rw [rateCoefficient, hfull]
      ring
    have hInnerRate'' : Tendsto
        (fun n : ℕ => Real.log
          (((iidSequenceLaw ν).innerMeasure
            {increment : ℕ → ℝ |
              RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
              probabilityRateDenominator 2 ν scale n)
        atTop (𝓝 (rateCoefficient 2 C * H')) := by
      simpa [hcoef'] using hInnerRate'
    have hOuterRate'' : Tendsto
        (fun n : ℕ => Real.log
          ((iidSequenceLaw ν
            {increment : ℕ → ℝ |
              RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
              probabilityRateDenominator 2 ν scale n)
        atTop (𝓝 (rateCoefficient 2 C * H')) := by
      simpa [hcoef'] using hOuterRate'
    exact hUnique H' ⟨A', hLimits', hEnergyEq', hInnerPos', hOuterPos',
      hPositive', hEnergyUpper', hInnerRate'', hOuterRate''⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Path

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Proof.Staircase.Concrete.Lower.Entrance
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Proof.Staircase.GlobalConditions
/-!
# Tilted-tube lower bound from global staircase conditions

The public theorem in this file is:

- `exists_concreteStaircaseLowerBound_of_globalConditions`:
  the robust entrance estimate and the global width, time, rate, and
  endpoint-margin inequalities imply
  $\mathbb P(E)\ge\exp(-d'L/\Delta^2)$.
  The ordinary and final blocks use their respective endpoint intervals.

This is the finite-block multiplication and common-threshold step in
Wang Yiyang, *Asymptotic speed of the $N$-branching random walk with infinite
offspring*, Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.SmallDeviation.Entrance
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The concrete staircase lower bound with blockwise conditions reduced to
inequalities at the global scale. -/
theorem exists_concreteStaircaseLowerBound_of_globalConditions
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma narrowedRate uInterior vInterior uFinal vFinal : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (m : ℕ) (hm : 2 ≤ m)
    (huInterior : 0 < uInterior)
    (huvInterior : uInterior < vInterior)
    (hvInterior : vInterior < 1)
    (huFinal : 0 < uFinal)
    (huvFinal : uFinal < vFinal)
    (hvFinal : vFinal < 1)
    (hrate : (Real.pi ^ 2 / 2) * sigma ^ 2 < narrowedRate) :
    ∃ width₀ ratio₀ : ℕ,
      ∀ (entrance horizon blockLength : ℕ)
        (margin globalWidth drift base endpointFraction
          blockRate totalRate : ℝ),
        entrance + 2 * blockLength ≤ horizon →
        0 < blockLength → 0 < globalWidth → 0 < margin →
        0 ≤ drift → 0 ≤ endpointFraction → 0 ≤ blockRate →
        10 * drift * (blockLength : ℝ) < globalWidth ^ 3 →
        width₀ ≤ ⌊staircaseBinWidth m * (globalWidth / 2)⌋₊ →
        1 / margin ≤ staircaseBinWidth m * (globalWidth / 2) →
        ratio₀ * ⌊staircaseBinWidth m * globalWidth⌋₊ ^ 2 ≤
          blockLength →
        narrowedRate * globalWidth ^ 2 ≤
          blockRate *
            (⌊staircaseBinWidth m *
              (globalWidth - 2 * drift * (blockLength : ℝ) /
                globalWidth ^ 2)⌋₊ : ℝ) ^ 2 →
        ((globalWidth / 3 +
            (2 / 3 : ℝ) *
              (2 * drift * (blockLength : ℝ) / globalWidth ^ 2)) /
            (globalWidth -
              2 * drift * (blockLength : ℝ) / globalWidth ^ 2)) /
          staircaseBinWidth m + margin ≤ uInterior →
        vInterior + margin ≤
          ((2 / 3 : ℝ) - 1 / (3 * (m : ℝ))) /
            staircaseBinWidth m →
        margin ≤ uFinal →
        vFinal + margin ≤
          (endpointFraction - 1 / (3 * (m : ℝ))) /
            staircaseBinWidth m →
        Real.exp (-(totalRate - blockRate) * (horizon : ℝ) /
          globalWidth ^ 2) ≤
          (iidSequenceLaw ν).real
            (robustMovingTransitionEvent entrance globalWidth drift
              (-base)) →
        Real.exp (-totalRate * (horizon : ℝ) / globalWidth ^ 2) ≤
          (iidSequenceLaw ν).real
            (driftedTubeEndpointWindowEvent horizon globalWidth drift
              base endpointFraction) := by
  obtain ⟨width₀, ratio₀, hfinite⟩ :=
    exists_concreteStaircaseLowerBound_of_robustEntrance
      hν hsigma m hm huInterior huvInterior hvInterior
        huFinal huvFinal hvFinal hrate
  refine ⟨width₀, ratio₀, ?_⟩
  intro entrance horizon blockLength margin globalWidth drift base
    endpointFraction blockRate totalRate hremaining hblockLength
    hglobalWidth hmargin hdrift hendpoint hblockRate hcost
    hfloorThreshold hmarginWidth htime hrate' hinteriorLower
    hinteriorUpper hfinalLower hfinalUpper hentranceProbability
  apply hfinite entrance horizon blockLength margin globalWidth drift
    base endpointFraction blockRate totalRate hremaining hblockLength
    hglobalWidth hmargin hdrift hblockRate hcost
  · exact staircaseBlockConditions_of_global (by omega)
      hblockLength hm hglobalWidth hdrift hendpoint hblockRate hcost
      hfloorThreshold hmarginWidth htime hrate' hinteriorLower
      hinteriorUpper hfinalLower hfinalUpper
  · exact hentranceProbability

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

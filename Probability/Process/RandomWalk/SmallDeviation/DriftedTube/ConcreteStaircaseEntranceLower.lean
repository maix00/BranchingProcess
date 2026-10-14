/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.ConcreteStaircaseLower
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.StaircaseEntranceBridge

/-!
# Concrete staircase lower bound after a robust entrance

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.exists_concreteStaircaseLowerBound_of_robustEntrance`:
  with $t_1+2\ell\le L$ and $10c\ell<\Delta^3$, a lower bound
  $\mathbb P(E_0^{\rm robust})\ge
  \exp(-(d'-d'')L/\Delta^2)$ and the finite-block rate conditions imply
  $\mathbb P(E)\ge\exp(-d'L/\Delta^2)$.

This is the final finite-block multiplication in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5. The robust entrance event is a subevent of
the Appendix A.2 transition event with terminal interval contained in the
first horizontal block's central window.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.SmallDeviation.Entrance
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The actual staircase schedule starts after a robust diffusive entrance;
its finite product then yields the target endpoint-window lower bound. -/
theorem exists_concreteStaircaseLowerBound_of_robustEntrance
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
        0 ≤ drift → 0 ≤ blockRate →
        10 * drift * (blockLength : ℝ) < globalWidth ^ 3 →
        (∀ j, j < staircaseBlockCount entrance horizon blockLength →
          let width := staircaseTubeWidth globalWidth drift
            (staircaseBlockLength entrance horizon blockLength) j
          let v₁ := staircaseEndpointLowerFraction
            (staircaseBlockCount entrance horizon blockLength)
            globalWidth drift
            (staircaseBlockLength entrance horizon blockLength) j
          let v₂ := staircaseEndpointUpperFraction
            (staircaseBlockCount entrance horizon blockLength)
            globalWidth drift endpointFraction
            (staircaseBlockLength entrance horizon blockLength) j
          let narrowedWidth := staircaseBinWidth m * width
          width₀ ≤ ⌊narrowedWidth⌋₊ ∧
          1 / margin ≤ narrowedWidth ∧
          ratio₀ * (⌊narrowedWidth⌋₊) ^ 2 ≤
            staircaseBlockLength entrance horizon blockLength j ∧
          narrowedRate * globalWidth ^ 2 ≤
            blockRate * (⌊narrowedWidth⌋₊ : ℝ) ^ 2 ∧
          (j + 1 < staircaseBlockCount entrance horizon blockLength →
            staircaseBinEndpointLowerFraction m v₁ + margin ≤
              uInterior ∧
            vInterior + margin ≤
              staircaseBinEndpointUpperFraction m v₂) ∧
          (¬j + 1 < staircaseBlockCount entrance horizon blockLength →
            staircaseBinEndpointLowerFraction m v₁ + margin ≤
              uFinal ∧
            vFinal + margin ≤
              staircaseBinEndpointUpperFraction m v₂)) →
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
    exists_concreteStaircaseLowerBound
      hν hsigma m hm huInterior huvInterior hvInterior
        huFinal huvFinal hvFinal hrate
  refine ⟨width₀, ratio₀, ?_⟩
  intro entrance horizon blockLength margin globalWidth drift base
    endpointFraction blockRate totalRate hremaining hblockLength
    hglobalWidth hmargin hdrift hblockRate hcost hparameters
    hentranceProbability
  let initial := robustMovingTransitionEvent entrance globalWidth drift (-base)
  have hcost' : 2 * drift * (blockLength : ℝ) < globalWidth ^ 3 := by
    have hnonneg : 0 ≤ drift * (blockLength : ℝ) := by positivity
    nlinarith [hcost]
  apply hfinite entrance horizon blockLength initial margin globalWidth
    drift base endpointFraction blockRate totalRate (by omega)
    hblockLength (by omega)
    (measurableSet_robustMovingTransitionEvent entrance globalWidth
      drift (-base))
    hglobalWidth hmargin hdrift hblockRate hcost'
  · intro increment hinc
    exact robustEntrance_entersFirstCentralWindow hremaining
      hblockLength hglobalWidth hdrift hcost hinc
  · exact hparameters
  · intro increment hinc time htime htimeUpper
    exact robustEntrance_staysInTiltedTube hinc time htime htimeUpper
  · exact hentranceProbability

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

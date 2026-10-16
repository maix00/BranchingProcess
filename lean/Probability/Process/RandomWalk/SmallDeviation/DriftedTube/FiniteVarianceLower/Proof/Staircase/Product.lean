/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Blocks.Assembly
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Proof.Staircase.Rate.BinRate
/-!
# Finite staircase probability from the endpoint-window rate

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.exists_uniform_staircaseProbability_ge_product`:
  for a fixed finite spatial-bin count, separate interior endpoint
  intervals for ordinary and final blocks, and the endpoint-window lower
  rate of Lemma 3.1(ii), the staircase conditions imply the entrance
  probability times the product of all block exponents.

This composes the narrowed-bin argument, central endpoint windows, and
reverse Markov product in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5. Its assumptions spell out the width,
terminal-margin, time-ratio, and global exponent comparisons for the
varying temporal blocks.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- Uniform narrowed-tube rates feed directly into the finite staircase
product under the quantitative block conditions in Wang Yiyang's proof of Lemma 3.5. -/
theorem exists_uniform_staircaseProbability_ge_product
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma d uInterior vInterior uFinal vFinal : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (m : ℕ) (hm : 2 ≤ m)
    (huInterior : 0 < uInterior)
    (huvInterior : uInterior < vInterior)
    (hvInterior : vInterior < 1)
    (huFinal : 0 < uFinal)
    (huvFinal : uFinal < vFinal)
    (hvFinal : vFinal < 1)
    (hd : (Real.pi ^ 2 / 2) * sigma ^ 2 < d) :
    ∃ width₀ ratio₀ : ℕ,
      ∀ (start length : ℕ → ℕ)
        (_hnext : ∀ j, start (j + 1) = start j + length j)
        (initial : Set (ℕ → ℝ))
        (_hinitial : MeasurableSet[sequencePrefixFiltration (E := ℝ) (start 0)]
          initial)
        (lower width v₁ v₂ : ℕ → ℝ)
        (margin globalWidth target : ℝ) (q : ℕ),
        0 < globalWidth → 0 < margin →
        (∀ j, j < q → 0 < width j) →
        (∀ increment ∈ initial,
          AdditivePath.displacement (start 0) increment ∈
            Set.Icc (lower 0 + width 0 / 3)
              (lower 0 + 2 * width 0 / 3)) →
        (∀ j, j + 1 < q →
          Set.Icc (lower j + v₁ j * width j)
            (lower j + v₂ j * width j) ⊆
          Set.Icc (lower (j + 1) + width (j + 1) / 3)
            (lower (j + 1) + 2 * width (j + 1) / 3)) →
        (∀ j, j < q →
          let narrowedWidth := staircaseBinWidth m * width j
          width₀ ≤ ⌊narrowedWidth⌋₊ ∧
          1 / margin ≤ narrowedWidth ∧
          ratio₀ * (⌊narrowedWidth⌋₊) ^ 2 ≤ length j ∧
          d * globalWidth ^ 2 ≤ target * (⌊narrowedWidth⌋₊ : ℝ) ^ 2 ∧
          (j + 1 < q →
            staircaseBinEndpointLowerFraction m (v₁ j) + margin ≤
              uInterior ∧
            vInterior + margin ≤
              staircaseBinEndpointUpperFraction m (v₂ j)) ∧
          (¬j + 1 < q →
            staircaseBinEndpointLowerFraction m (v₁ j) + margin ≤
              uFinal ∧
            vFinal + margin ≤
              staircaseBinEndpointUpperFraction m (v₂ j))) →
          (iidSequenceLaw ν).real initial *
            (∏ j ∈ Finset.range q,
              Real.exp (-target * (length j : ℝ) / globalWidth ^ 2)) ≤
          (iidSequenceLaw ν).real
            (initial ∩ conditionalBlockIntersection
              (fun j => tubeBlockEvent (start j) (length j)
                (lower j) (width j) (v₁ j) (v₂ j)) q) := by
  obtain ⟨widthInterior, ratioInterior, hrateInterior⟩ :=
    exists_uniform_staircaseBinProbability_ge_exp
      hν hsigma m hm huInterior huvInterior hvInterior hd
  obtain ⟨widthFinal, ratioFinal, hrateFinal⟩ :=
    exists_uniform_staircaseBinProbability_ge_exp
      hν hsigma m hm huFinal huvFinal hvFinal hd
  refine ⟨max widthInterior widthFinal,
    max ratioInterior ratioFinal, ?_⟩
  intro start length hnext initial hinitial lower width v₁ v₂
    margin globalWidth target q hglobalWidth hmargin hwidth
    hfirst hwindow hparameters
  have hnarrowed : ∀ j, j < q →
      0 < staircaseBinWidth m * width j := by
    intro j hj
    exact mul_pos (staircaseBinWidth_pos hm) (hwidth j hj)
  have hbins : ∀ j, j < q → ∀ l : ℕ, l < m →
      Real.exp (-target * (length j : ℝ) / globalWidth ^ 2) ≤
        (iidSequenceLaw ν).real
          (horizontalTubeEndpointWindowEvent
            (staircaseBinTubeParameter m l)
            (staircaseBinWidth m * width j) (length j)
            (staircaseBinEndpointLowerFraction m (v₁ j))
            (staircaseBinEndpointUpperFraction m (v₂ j))) := by
    intro j hj l hl
    obtain ⟨hwidthFloor, hwidthMargin, hratio, hscale,
      hmarginInterior, hmarginFinal⟩ := hparameters j hj
    have hsource : ENNReal.ofReal
        (Real.exp (-target * (length j : ℝ) / globalWidth ^ 2)) ≤
        horizontalTubeEndpointWindowProbability
          (iidSequenceLaw ν) (staircaseBinTubeParameter m l)
          (staircaseBinWidth m * width j) (length j)
          (staircaseBinEndpointLowerFraction m (v₁ j))
          (staircaseBinEndpointUpperFraction m (v₂ j)) := by
      by_cases hbefore : j + 1 < q
      · obtain ⟨hmarginLower, hmarginUpper⟩ := hmarginInterior hbefore
        exact hrateInterior
          (staircaseBinWidth m * width j) (v₁ j) (v₂ j)
          margin globalWidth target (hnarrowed j hj) hmargin hglobalWidth
          ((le_max_left _ _).trans hwidthFloor) hwidthMargin
          hmarginLower hmarginUpper hscale (length j)
          ((Nat.mul_le_mul_right _ (le_max_left _ _)).trans hratio) l hl
      · obtain ⟨hmarginLower, hmarginUpper⟩ := hmarginFinal hbefore
        exact hrateFinal
          (staircaseBinWidth m * width j) (v₁ j) (v₂ j)
          margin globalWidth target (hnarrowed j hj) hmargin hglobalWidth
          ((le_max_right _ _).trans hwidthFloor) hwidthMargin
          hmarginLower hmarginUpper hscale (length j)
          ((Nat.mul_le_mul_right _ (le_max_right _ _)).trans hratio) l hl
    have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hsource
    change Real.exp (-target * (length j : ℝ) / globalWidth ^ 2) ≤
      ((iidSequenceLaw ν)
        (horizontalTubeEndpointWindowEvent
          (staircaseBinTubeParameter m l)
          (staircaseBinWidth m * width j) (length j)
          (staircaseBinEndpointLowerFraction m (v₁ j))
          (staircaseBinEndpointUpperFraction m (v₂ j)))).toReal
    simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hreal
  exact measureReal_staircaseBlockIntersection_ge_prod_of_binBounds
    ν start length hnext initial hinitial lower width v₁ v₂
      (fun j => Real.exp (-target * (length j : ℝ) / globalWidth ^ 2))
      q hwidth hfirst hwindow (fun j => (Real.exp_pos _).le)
      m hm hbins

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

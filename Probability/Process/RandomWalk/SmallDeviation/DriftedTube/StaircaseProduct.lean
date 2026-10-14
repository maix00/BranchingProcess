/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.BlockAssembly
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.StaircaseBinRate

/-!
# Finite staircase probability from the endpoint-window rate

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.exists_uniform_staircaseProbability_ge_product`:
  for a fixed finite spatial-bin count, the endpoint-window lower rate of
  Lemma 3.1(ii) and the paper's numeric staircase conditions imply the
  entrance probability times the product of all block exponents.

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
product under the quantitative block conditions in the thesis proof. -/
theorem exists_uniform_staircaseProbability_ge_product
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma d u v : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (m : ℕ) (hm : 2 ≤ m)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
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
          staircaseBinEndpointLowerFraction m (v₁ j) + margin ≤ u ∧
          v + margin ≤ staircaseBinEndpointUpperFraction m (v₂ j) ∧
          ratio₀ * (⌊narrowedWidth⌋₊) ^ 2 ≤ length j ∧
          d * globalWidth ^ 2 ≤ target * (⌊narrowedWidth⌋₊ : ℝ) ^ 2) →
          (iidSequenceLaw ν).real initial *
            (∏ j ∈ Finset.range q,
              Real.exp (-target * (length j : ℝ) / globalWidth ^ 2)) ≤
          (iidSequenceLaw ν).real
            (initial ∩ conditionalBlockIntersection
              (fun j => tubeBlockEvent (start j) (length j)
                (lower j) (width j) (v₁ j) (v₂ j)) q) := by
  obtain ⟨width₀, ratio₀, hrate⟩ :=
    exists_uniform_staircaseBinProbability_ge_exp
      hν hsigma m hm hu huv hv hd
  refine ⟨width₀, ratio₀, ?_⟩
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
    obtain ⟨hwidthFloor, hwidthMargin, hmarginLower,
      hmarginUpper, hratio, hscale⟩ := hparameters j hj
    have hsource := hrate
      (staircaseBinWidth m * width j) (v₁ j) (v₂ j)
      margin globalWidth target (hnarrowed j hj) hmargin hglobalWidth
      hwidthFloor hwidthMargin hmarginLower hmarginUpper hscale
      (length j) hratio l hl
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

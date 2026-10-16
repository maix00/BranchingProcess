/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Blocks.Exponent
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Proof.Staircase.Inclusion
/-!
# Finite staircase lower bound with a diffusive entrance

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.exists_uniform_finiteStaircaseLowerBound`:
  if the diffusive entrance probability pays at most
  $\exp(-(d'-d'')L/D^2)$ and the quantitative staircase conditions of Wang Yiyang's Lemma 3.5
  hold, then the tilted-tube endpoint probability is at least
  $\exp(-d'L/D^2)$.

This is the finite-stage probability calculation in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5. The theorem exposes the concrete schedule
inequalities and entrance estimate that must be verified for Wang Yiyang's Lemma 3.5
parameters; it does not replace the conditioned Brownian-meander input.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The entrance estimate, finite spatial-bin rate, reverse Markov product,
and event inclusion yield the tilted-tube endpoint lower bound. -/
theorem exists_uniform_finiteStaircaseLowerBound
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
      ∀ (start length : ℕ → ℕ)
        (_hnext : ∀ j, start (j + 1) = start j + length j)
        (q horizon : ℕ)
        (_hq : 0 < q) (_hfinish : start q = horizon)
        (initial : Set (ℕ → ℝ))
        (_hinitial : MeasurableSet[sequencePrefixFiltration (E := ℝ)
          (start 0)] initial)
        (blockLower blockWidth v₁ v₂ : ℕ → ℝ)
        (margin globalWidth drift base endpointFraction
          blockRate totalRate : ℝ),
        0 < globalWidth → 0 < margin → 0 ≤ drift → 0 ≤ blockRate →
        (∀ j, j < q → 0 < blockWidth j) →
        (∀ increment ∈ initial,
          AdditivePath.displacement (start 0) increment ∈
            Set.Icc (blockLower 0 + blockWidth 0 / 3)
              (blockLower 0 + 2 * blockWidth 0 / 3)) →
        (∀ j, j + 1 < q →
          Set.Icc (blockLower j + v₁ j * blockWidth j)
            (blockLower j + v₂ j * blockWidth j) ⊆
          Set.Icc (blockLower (j + 1) + blockWidth (j + 1) / 3)
            (blockLower (j + 1) + 2 * blockWidth (j + 1) / 3)) →
        (∀ j, j < q →
          let narrowedWidth := staircaseBinWidth m * blockWidth j
          width₀ ≤ ⌊narrowedWidth⌋₊ ∧
          1 / margin ≤ narrowedWidth ∧
          ratio₀ * (⌊narrowedWidth⌋₊) ^ 2 ≤ length j ∧
          narrowedRate * globalWidth ^ 2 ≤
            blockRate * (⌊narrowedWidth⌋₊ : ℝ) ^ 2 ∧
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
        (∀ j, j < q → blockLower j =
          base + drift * ((start j + length j : ℕ) : ℝ) /
            globalWidth ^ 2) →
        (∀ j, j < q → blockLower j + blockWidth j =
          base + drift * (start j : ℝ) / globalWidth ^ 2 +
            globalWidth) →
        (∀ increment ∈ initial, ∀ time : ℕ,
          1 ≤ time → time ≤ start 0 →
            base + drift * (time : ℝ) / globalWidth ^ 2 ≤
              AdditivePath.displacement time increment ∧
            AdditivePath.displacement time increment ≤
              base + drift * (time : ℝ) / globalWidth ^ 2 +
                globalWidth) →
        Set.Icc
          (blockLower (q - 1) + v₁ (q - 1) * blockWidth (q - 1))
          (blockLower (q - 1) + v₂ (q - 1) * blockWidth (q - 1)) ⊆
          Set.Icc
            (base + drift * (horizon : ℝ) / globalWidth ^ 2)
            (base + drift * (horizon : ℝ) / globalWidth ^ 2 +
              endpointFraction * globalWidth) →
        Real.exp (-(totalRate - blockRate) * (horizon : ℝ) /
          globalWidth ^ 2) ≤ (iidSequenceLaw ν).real initial →
        Real.exp (-totalRate * (horizon : ℝ) / globalWidth ^ 2) ≤
          (iidSequenceLaw ν).real
            (driftedTubeEndpointWindowEvent horizon globalWidth drift
              base endpointFraction) := by
  obtain ⟨width₀, ratio₀, hstaircase⟩ :=
    exists_uniform_staircaseProbability_ge_product
      hν hsigma m hm huInterior huvInterior hvInterior
        huFinal huvFinal hvFinal hrate
  refine ⟨width₀, ratio₀, ?_⟩
  intro start length hnext q horizon hq hfinish initial hinitial
    blockLower blockWidth v₁ v₂ margin globalWidth drift base
    endpointFraction blockRate totalRate hglobalWidth hmargin
    hdrift hblockRate hwidth hfirst hwindow hparameters
    hblockLower hblockUpper hentrance hfinalWindow hentranceProbability
  let events : ℕ → Set (ℕ → ℝ) := fun j =>
    tubeBlockEvent (start j) (length j)
      (blockLower j) (blockWidth j) (v₁ j) (v₂ j)
  have hproduct := hstaircase start length hnext initial hinitial
    blockLower blockWidth v₁ v₂ margin globalWidth blockRate q
    hglobalWidth hmargin hwidth hfirst hwindow hparameters
  have hlength : start 0 ≤ horizon := by
    have h := sum_blockLengths_add_start start length hnext q
    rw [hfinish] at h
    omega
  have hproduct' :
      (iidSequenceLaw ν).real initial *
          Real.exp (-blockRate * ((horizon - start 0 : ℕ) : ℝ) /
            globalWidth ^ 2) ≤
        (iidSequenceLaw ν).real
          (initial ∩ conditionalBlockIntersection events q) := by
    simpa only [events, prod_exp_blockLengths start length hnext q
      blockRate globalWidth, hfinish] using hproduct
  have hinclusion : initial ∩ conditionalBlockIntersection events q ⊆
      driftedTubeEndpointWindowEvent horizon globalWidth drift
        base endpointFraction :=
    initialInterTubeBlocks_subset_driftedTubeEndpointWindowEvent
      start length hnext q horizon hq hfinish initial globalWidth
      drift base endpointFraction hdrift blockLower blockWidth v₁ v₂
      hblockLower hblockUpper hentrance hfinalWindow
  have hmeasureMono :
      (iidSequenceLaw ν)
          (initial ∩ conditionalBlockIntersection events q) ≤
        (iidSequenceLaw ν)
          (driftedTubeEndpointWindowEvent horizon globalWidth drift
            base endpointFraction) :=
    measure_mono hinclusion
  have hprobabilityMono := ENNReal.toReal_mono
    (measure_ne_top _ _) hmeasureMono
  calc
    Real.exp (-totalRate * (horizon : ℝ) / globalWidth ^ 2) ≤
        Real.exp (-(totalRate - blockRate) * (horizon : ℝ) /
          globalWidth ^ 2) *
          Real.exp (-blockRate * ((horizon - start 0 : ℕ) : ℝ) /
            globalWidth ^ 2) :=
      exp_totalCost_le_mul_entrance_blockCost hlength hblockRate
    _ ≤ (iidSequenceLaw ν).real initial *
          Real.exp (-blockRate * ((horizon - start 0 : ℕ) : ℝ) /
            globalWidth ^ 2) :=
      mul_le_mul_of_nonneg_right hentranceProbability
        (Real.exp_pos _).le
    _ ≤ (iidSequenceLaw ν).real
        (initial ∩ conditionalBlockIntersection events q) := hproduct'
    _ ≤ (iidSequenceLaw ν).real
        (driftedTubeEndpointWindowEvent horizon globalWidth drift
          base endpointFraction) := hprobabilityMono

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Algebra.BigOperators.AdditivePath.Basic
public import Probability.Distributions.Moments.Real
public import Probability.Sequence.Filtration
public import Probability.Sequence.IID.Basic
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Setup.Binning
public import Probability.Process.RandomWalk.Path.Block.Partition.TailMerged
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Setup.BlockTube
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.EndpointEvent
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Reflection
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Rate.BlockExponential
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Cost
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.FiniteLower
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Endpoint.UpperInclusion
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Product
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Setup.Binning

/-!
# Finite staircase lower bound with an upper terminal window

The module-visible supporting lemma in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.exists_uniform_finiteStaircaseUpperEndpointLowerBound`:
  the entrance estimate, the same uniform horizontal-block product as
  for the lower terminal window, and upper-window inclusion imply
  $\mathbb P(E_{\rm upper})\ge\exp(-d'L/\Delta^2)$.

This is the symmetric endpoint construction in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, proof of Lemma 3.5. The horizontal-block probability estimate
is reused through `exists_uniform_staircaseProbability_ge_product`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

open ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

/-- The finite staircase calculation with a final window adjacent to the
upper edge of the tilted tube. -/
lemma exists_uniform_finiteStaircaseUpperEndpointLowerBound
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
        0 < globalWidth → 0 < margin → 0 ≤ blockRate →
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
        (∀ j, j < q → blockLower j = base +
          max (drift * (start j : ℝ) / globalWidth ^ 2)
            (drift * ((start j + length j : ℕ) : ℝ) / globalWidth ^ 2)) →
        (∀ j, j < q → blockLower j + blockWidth j = base +
          min (drift * (start j : ℝ) / globalWidth ^ 2)
            (drift * ((start j + length j : ℕ) : ℝ) /
              globalWidth ^ 2) + globalWidth) →
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
          Set.Icc (base + drift * (horizon : ℝ) / globalWidth ^ 2)
            (base + drift * (horizon : ℝ) / globalWidth ^ 2 +
              globalWidth) →
        Set.Icc
          (blockLower (q - 1) + v₁ (q - 1) * blockWidth (q - 1))
          (blockLower (q - 1) + v₂ (q - 1) * blockWidth (q - 1)) ⊆
          Set.Icc
            (base + drift * (horizon : ℝ) / globalWidth ^ 2 +
              globalWidth - endpointFraction * globalWidth)
            (base + drift * (horizon : ℝ) / globalWidth ^ 2 +
              globalWidth) →
        Real.exp (-(totalRate - blockRate) * (horizon : ℝ) /
          globalWidth ^ 2) ≤ (iidSequenceLaw ν).real initial →
        Real.exp (-totalRate * (horizon : ℝ) / globalWidth ^ 2) ≤
          (iidSequenceLaw ν).real
            (driftedTubeUpperEndpointWindowEvent horizon globalWidth
              drift base endpointFraction) := by
  obtain ⟨width₀, ratio₀, hstaircase⟩ :=
    exists_uniform_staircaseProbability_ge_product
      hν hsigma m hm huInterior huvInterior hvInterior
        huFinal huvFinal hvFinal hrate
  refine ⟨width₀, ratio₀, ?_⟩
  intro start length hnext q horizon hq hfinish initial hinitial
    blockLower blockWidth v₁ v₂ margin globalWidth drift base
    endpointFraction blockRate totalRate hglobalWidth hmargin
    hblockRate hwidth hfirst hwindow hparameters hblockLower
    hblockUpper hentrance hfinalFull hfinalUpper hentranceProbability
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
      driftedTubeUpperEndpointWindowEvent horizon globalWidth drift
        base endpointFraction :=
    initialInterTubeBlocks_subset_driftedTubeUpperEndpointWindowEvent
      start length hnext q horizon hq hfinish initial globalWidth
      drift base endpointFraction blockLower blockWidth v₁ v₂
      hblockLower hblockUpper hentrance hfinalFull hfinalUpper
  have hmeasureMono :
      (iidSequenceLaw ν)
          (initial ∩ conditionalBlockIntersection events q) ≤
        (iidSequenceLaw ν)
          (driftedTubeUpperEndpointWindowEvent horizon globalWidth drift
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
        (driftedTubeUpperEndpointWindowEvent horizon globalWidth drift
          base endpointFraction) := hprobabilityMono

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

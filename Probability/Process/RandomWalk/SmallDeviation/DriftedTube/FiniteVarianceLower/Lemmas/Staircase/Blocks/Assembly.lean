/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Blocks.Probability
public import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.Blocks.Geometry
/-!
# Staircase block probability assembly

The module-visible lemma in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.measureReal_staircaseBlockIntersection_ge_prod_of_binBounds`:
  an entrance event into the first central window, containment of each
  endpoint window in the next central window, and uniform probability
  bounds for the finitely many narrowed tubes yield
  $\mathbb P(E_0\cap\bigcap_{j<q}E_j)\ge
  \mathbb P(E_0)\prod_{j<q}p_j$.

This is the finite-bin selection followed by reverse Markov multiplication
in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, proof of Lemma 3.5. The fixed-bin bounds
are the precise remaining rate input from Lemma 3.1(ii).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

open ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- Finitely many narrowed-tube probability bounds and the central endpoint
windows give the complete finite staircase probability product. -/
lemma measureReal_staircaseBlockIntersection_ge_prod_of_binBounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ → ℕ)
    (hnext : ∀ j, start (j + 1) = start j + length j)
    (initial : Set (ℕ → ℝ))
    (hinitial : MeasurableSet[sequencePrefixFiltration (E := ℝ) (start 0)]
      initial)
    (lower width v₁ v₂ bounds : ℕ → ℝ)
    (q : ℕ)
    (hwidth : ∀ j, j < q → 0 < width j)
    (hfirst : ∀ increment ∈ initial,
      AdditivePath.displacement (start 0) increment ∈
        Set.Icc (lower 0 + width 0 / 3)
          (lower 0 + 2 * width 0 / 3))
    (hwindow : ∀ j, j + 1 < q →
      Set.Icc (lower j + v₁ j * width j)
        (lower j + v₂ j * width j) ⊆
      Set.Icc (lower (j + 1) + width (j + 1) / 3)
        (lower (j + 1) + 2 * width (j + 1) / 3))
    (hboundNonneg : ∀ j, 0 ≤ bounds j)
    (m : ℕ) (hm : 2 ≤ m)
    (hbins : ∀ j, j < q → ∀ l : ℕ, l < m →
      bounds j ≤ (iidSequenceLaw ν).real
        (horizontalTubeEndpointWindowEvent
          (staircaseBinTubeParameter m l)
          (staircaseBinWidth m * width j) (length j)
          (staircaseBinEndpointLowerFraction m (v₁ j))
          (staircaseBinEndpointUpperFraction m (v₂ j)))) :
    (iidSequenceLaw ν).real initial *
      (∏ j ∈ Finset.range q, bounds j) ≤
      (iidSequenceLaw ν).real
        (initial ∩ conditionalBlockIntersection
          (fun j => tubeBlockEvent (start j) (length j)
            (lower j) (width j) (v₁ j) (v₂ j)) q) := by
  let good : ℕ → Set ℝ := fun j =>
    Set.Icc (lower j + width j / 3)
      (lower j + 2 * width j / 3)
  have hgoodTube : ∀ j, j < q → good j ⊆
      Set.Icc (lower j) (lower j + width j) := by
    intro j hj position hposition
    have hw := hwidth j hj
    exact ⟨by dsimp [good] at hposition; linarith [hposition.1],
      by dsimp [good] at hposition; linarith [hposition.2]⟩
  have hblockBound : ∀ j, j < q → ∀ position, position ∈ good j →
      bounds j ≤ (iidSequenceLaw ν).real
        (relativeHorizontalTubeEndpointWindowEvent
          (lower j - position) (width j) (length j) (v₁ j) (v₂ j)) := by
    intro j hj position hp
    exact relativeHorizontalTubeProbability_ge_of_staircaseBinBounds
      ν hm (hwidth j hj) (fun l hl => hbins j hj l hl) position hp
  exact measureReal_tubeBlockIntersection_ge_prod_of_endpointWindows
    ν start length hnext initial hinitial lower width v₁ v₂ bounds
      good q hgoodTube hfirst hwindow hboundNonneg hblockBound

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

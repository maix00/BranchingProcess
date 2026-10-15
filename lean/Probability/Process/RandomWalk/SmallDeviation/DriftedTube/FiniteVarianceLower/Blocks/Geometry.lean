/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Blocks.Product
/-!
# Consecutive horizontal tube windows

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.tubeBlockIntersection_enters_next`:
  if the entrance event ends in the first tube and each block's endpoint
  window lies inside the following tube, then every successful prefix
  starts its next block inside that tube.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.measureReal_tubeBlockIntersection_ge_prod_of_endpointWindows`:
  the endpoint-window containments and one-block probability estimates
  yield the product lower bound with the entrance-event factor.

This is the window-containment step in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The endpoint window of the preceding horizontal block supplies the
starting-point hypothesis for the next block. -/
theorem tubeBlockIntersection_enters_next
    (start length : ℕ → ℕ)
    (hnext : ∀ j, start (j + 1) = start j + length j)
    (initial : Set (ℕ → ℝ))
    (lower width v₁ v₂ : ℕ → ℝ)
    (good : ℕ → Set ℝ)
    (q : ℕ)
    (hfirst : ∀ increment ∈ initial,
      AdditivePath.displacement (start 0) increment ∈ good 0)
    (hwindow : ∀ j, j + 1 < q →
      Set.Icc (lower j + v₁ j * width j)
        (lower j + v₂ j * width j) ⊆ good (j + 1)) :
    ∀ j, j < q → ∀ increment : ℕ → ℝ,
      increment ∈ initial ∩ conditionalBlockIntersection
        (fun i => tubeBlockEvent (start i) (length i)
          (lower i) (width i) (v₁ i) (v₂ i)) j →
      (∑ k : Fin (start j),
        Combinatorics.Sequence.blockCoordinates 0
          (start j) increment k) ∈ good j := by
  intro j hjq increment hj
  have hprefix :
      (∑ k : Fin (start j),
        Combinatorics.Sequence.blockCoordinates 0
          (start j) increment k) =
      AdditivePath.displacement (start j) increment := by
    simp [Combinatorics.Sequence.blockCoordinates,
      AdditivePath.displacement, Fin.sum_univ_eq_sum_range]
  rw [hprefix]
  cases j with
  | zero => exact hfirst increment hj.1
  | succ k =>
      have hprevious : increment ∈
          tubeBlockEvent (start k) (length k)
            (lower k) (width k) (v₁ k) (v₂ k) := hj.2.2
      have hend := tubeBlockEvent_end_mem hprevious
      rw [hnext k]
      exact hwindow k hjq hend

/-- The reverse Markov multiplication in Wang Yiyang's Lemma 3.5 for successive horizontal
tubes, including the entrance event and unequal block lengths. -/
theorem measureReal_tubeBlockIntersection_ge_prod_of_endpointWindows
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ → ℕ)
    (hnext : ∀ j, start (j + 1) = start j + length j)
    (initial : Set (ℕ → ℝ))
    (hinitial : MeasurableSet[sequencePrefixFiltration (E := ℝ) (start 0)]
      initial)
    (lower width v₁ v₂ bounds : ℕ → ℝ)
    (good : ℕ → Set ℝ)
    (q : ℕ)
    (hgoodTube : ∀ j, j < q → good j ⊆
      Set.Icc (lower j) (lower j + width j))
    (hfirst : ∀ increment ∈ initial,
      AdditivePath.displacement (start 0) increment ∈ good 0)
    (hwindow : ∀ j, j + 1 < q →
      Set.Icc (lower j + v₁ j * width j)
        (lower j + v₂ j * width j) ⊆ good (j + 1))
    (hboundNonneg : ∀ j, 0 ≤ bounds j)
    (hblockBound : ∀ j, j < q → ∀ initial,
      initial ∈ good j →
        bounds j ≤ (iidSequenceLaw ν).real
          (relativeHorizontalTubeEndpointWindowEvent
          (lower j - initial) (width j) (length j) (v₁ j) (v₂ j))) :
    (iidSequenceLaw ν).real initial *
      (∏ j ∈ Finset.range q, bounds j) ≤
      (iidSequenceLaw ν).real
        (initial ∩ conditionalBlockIntersection
          (fun j => tubeBlockEvent (start j) (length j)
            (lower j) (width j) (v₁ j) (v₂ j)) q) := by
  exact measureReal_tubeBlockIntersection_ge_prod ν start length hnext
    initial hinitial lower width v₁ v₂ bounds good q hgoodTube
      hboundNonneg hblockBound
    (tubeBlockIntersection_enters_next start length hnext initial
      lower width v₁ v₂ good q hfirst hwindow)

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

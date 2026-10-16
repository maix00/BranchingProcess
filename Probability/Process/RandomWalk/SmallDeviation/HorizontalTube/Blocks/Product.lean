/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.Blocks.EventBridge
/-!
# Product lower bound for horizontal tube blocks

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.measureReal_tubeBlockIntersection_ge_prod`:
  if an initial entrance event $E_0$ and the preceding blocks place the
  walk inside the next horizontal tube, and each translated one-block
  probability is at least $p_j$, then
  $\mathbb P(E_0\cap\bigcap_{j<q}E_j)\ge
  \mathbb P(E_0)\prod_{j<q}p_j$.

This is the reverse Markov product in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, proof of Lemma 3.5. The next-tube inclusion is supplied by the
staircase geometry in the same proof.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube


/-- Successive horizontal tube blocks multiply their conditional lower
bounds when each successful prefix enters the next tube. -/
theorem measureReal_tubeBlockIntersection_ge_prod
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
    (hboundNonneg : ∀ j, 0 ≤ bounds j)
    (hblockBound : ∀ j, j < q → ∀ initial,
      initial ∈ good j →
        bounds j ≤ (iidSequenceLaw ν).real
          (relativeHorizontalTubeEndpointWindowEvent
          (lower j - initial) (width j) (length j) (v₁ j) (v₂ j)))
    (henter : ∀ j, j < q → ∀ increment : ℕ → ℝ,
      increment ∈ initial ∩ conditionalBlockIntersection
        (fun i => tubeBlockEvent (start i) (length i)
          (lower i) (width i) (v₁ i) (v₂ i)) j →
      (∑ k : Fin (start j),
        Combinatorics.Sequence.blockCoordinates 0
          (start j) increment k) ∈ good j) :
    (iidSequenceLaw ν).real initial *
      (∏ j ∈ Finset.range q, bounds j) ≤
      (iidSequenceLaw ν).real
        (initial ∩ conditionalBlockIntersection
          (fun j => tubeBlockEvent (start j) (length j)
            (lower j) (width j) (v₁ j) (v₂ j)) q) := by
  let events : ℕ → Set (ℕ → ℝ) := fun j =>
    tubeBlockEvent (start j) (length j)
      (lower j) (width j) (v₁ j) (v₂ j)
  let filtration : ℕ → MeasurableSpace (ℕ → ℝ) := fun j =>
    sequencePrefixFiltration (E := ℝ) (start j)
  have hfiltrationMono : ∀ j,
      filtration j ≤ filtration (j + 1) := by
    intro j
    dsimp [filtration]
    apply (sequencePrefixFiltration (E := ℝ)).mono'
    rw [hnext j]
    exact Nat.le_add_right _ _
  have hfiltrationAmbient : ∀ j,
      filtration j ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) := by
    intro j
    exact (sequencePrefixFiltration (E := ℝ)).le' (start j)
  have heventMeasurable : ∀ j,
      MeasurableSet[filtration (j + 1)] (events j) := by
    intro j
    change MeasurableSet[sequencePrefixFiltration (E := ℝ)
      (start (j + 1))]
      (tubeBlockEvent (start j) (length j)
        (lower j) (width j) (v₁ j) (v₂ j))
    rw [hnext j]
    exact measurableSet_tubeBlockEvent
      (start j) (length j)
        (lower j) (width j) (v₁ j) (v₂ j)
  have hconditional : ∀ j, j < q → ∀ᵐ increment ∂iidSequenceLaw ν,
      increment ∈ initial ∩ conditionalBlockIntersection events j →
        bounds j ≤ condExp (filtration j) (iidSequenceLaw ν)
          ((events j).indicator fun _ => (1 : ℝ)) increment := by
    intro j hj
    have h := iidSequenceLaw_condExp_tubeBlockEvent_ge
      ν (lower j) (width j) (v₁ j) (v₂ j)
        (start j) (length j) (good j) (hgoodTube j hj)
          (hblockBound j hj)
    filter_upwards [h] with increment hstep hpast
    exact hstep (henter j hj increment hpast)
  exact measureReal_initialInterConditionalBlockIntersection_ge_mul_prod_prefix
    filtration hfiltrationMono hfiltrationAmbient initial hinitial events
      bounds hboundNonneg q (fun j _ => heventMeasurable j) hconditional

end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

end

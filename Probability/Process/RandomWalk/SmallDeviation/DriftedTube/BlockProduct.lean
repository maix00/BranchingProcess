/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.BlockEventBridge

/-!
# Product lower bound for horizontal tube blocks

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.measureReal_tubeBlockIntersection_ge_prod`:
  if the preceding blocks place the walk inside the next horizontal tube
  and each translated one-block probability is at least $p_j$, then
  $\mathbb P(\bigcap_{j<q}E_j)\ge\prod_{j<q}p_j$.

This is the reverse Markov product in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5. The next-tube inclusion is supplied by the
staircase geometry in the same proof.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- Successive horizontal tube blocks multiply their conditional lower
bounds when each successful prefix enters the next tube. -/
theorem measureReal_tubeBlockIntersection_ge_prod
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ → ℕ)
    (hnext : ∀ j, start (j + 1) = start j + length j)
    (lower width v₁ v₂ bounds : ℕ → ℝ)
    (hboundNonneg : ∀ j, 0 ≤ bounds j)
    (hblockBound : ∀ j initial,
      initial ∈ Set.Icc (lower j) (lower j + width j) →
        bounds j ≤ (iidSequenceLaw ν).real
          (relativeHorizontalTubeEndpointWindowEvent
          (lower j - initial) (width j) (length j) (v₁ j) (v₂ j)))
    (henter : ∀ j (increment : ℕ → ℝ),
      increment ∈ conditionalBlockIntersection
        (fun i => tubeBlockEvent (start i) (length i)
          (lower i) (width i) (v₁ i) (v₂ i)) j →
      (∑ k : Fin (start j),
        Combinatorics.Sequence.blockCoordinates 0
          (start j) increment k) ∈
        Set.Icc (lower j) (lower j + width j))
    (q : ℕ) :
    (∏ j ∈ Finset.range q, bounds j) ≤
      (iidSequenceLaw ν).real
        (conditionalBlockIntersection
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
  have hconditional : ∀ j, ∀ᵐ increment ∂iidSequenceLaw ν,
      increment ∈ conditionalBlockIntersection events j →
        bounds j ≤ condExp (filtration j) (iidSequenceLaw ν)
          ((events j).indicator fun _ => (1 : ℝ)) increment := by
    intro j
    have h := iidSequenceLaw_condExp_tubeBlockEvent_ge
      ν (lower j) (width j) (v₁ j) (v₂ j)
        (start j) (length j) (hblockBound j)
    filter_upwards [h] with increment hstep hpast
    exact hstep (henter j increment hpast)
  exact measureReal_conditionalBlockIntersection_ge_prod
    filtration hfiltrationMono hfiltrationAmbient events
      heventMeasurable bounds hboundNonneg hconditional q

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

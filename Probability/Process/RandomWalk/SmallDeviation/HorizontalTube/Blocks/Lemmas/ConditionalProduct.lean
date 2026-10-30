/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.Filtration.ConditionalBlocks
import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.Blocks.EventBridge
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Probability.Sequence.Filtration
import Probability.Sequence.IID.Blocks.StoppingTime
import Probability.Sequence.IID.Blocks.Consecutive
import Probability.Independence.ConditionalIntegral
/-!
# Product lower bound for horizontal tube blocks

## Internal proof declarations

This package-private proof chain specializes the generic conditional-block
product theorem to horizontal-tube events. The two conditional-expectation
steps transfer the translated one-block bound to the past-dependent path event;
the product conclusion is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.measureReal_tubeBlockIntersection_ge_prod`:
  if an initial entrance event $E_0$ and the preceding blocks place the
  walk inside the next horizontal tube, and each translated one-block
  probability is at least $p_j$, then
  $\mathbb P(E_0\cap\bigcap_{j<q}E_j)\ge
  \mathbb P(E_0)\prod_{j<q}p_j$.

The supporting declarations are private: iidSequenceLaw_condExp_tubeBlockPairEvent_ge
and iidSequenceLaw_condExp_tubeBlockEvent_ge express the same one-block
conditional lower bound on the pair and whole-path event forms.

This is the reverse Markov product in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, proof of Lemma 3.5. The next-tube inclusion is supplied by the
staircase geometry in the same proof. The reusable generic conditional-block
product theorem remains in `Probability.Process.Filtration.ConditionalBlocks`.
-/

section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube


/-- The Markov step in the horizontal-block argument: conditionally on the
preceding position lying inside the tube, the chance of the next finite
block is bounded by its translated zero-start probability. -/
private lemma iidSequenceLaw_condExp_tubeBlockPairEvent_ge
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (lower width v₁ v₂ : ℝ) (start length : ℕ)
    (good : Set ℝ)
    (hgoodTube : good ⊆ Set.Icc lower (lower + width))
    {bound : ℝ}
    (hbound : ∀ initial ∈ good,
      bound ≤ (iidSequenceLaw ν).real
        (relativeHorizontalTubeEndpointWindowEvent
          (lower - initial) width length v₁ v₂)) :
    ∀ᵐ increment ∂iidSequenceLaw ν,
      (∑ j : Fin start,
          Combinatorics.Sequence.blockCoordinates 0 start increment j) ∈
        good →
      bound ≤ condExp
        (MeasurableSpace.comap
          (Combinatorics.Sequence.blockCoordinates 0 start) inferInstance)
        (iidSequenceLaw ν)
        (fun increment =>
          (tubeBlockPairEvent lower width v₁ v₂ start length).indicator
            (fun _ => (1 : ℝ))
            (Combinatorics.Sequence.blockCoordinates 0 start increment,
              Combinatorics.Sequence.blockCoordinates start length increment))
        increment := by
  let goodPast : Set (Fin start → ℝ) :=
    {past | (∑ j : Fin start, past j) ∈ good}
  have hsections : ∀ past : Fin start → ℝ, past ∈ goodPast →
      bound ≤ ((iidSequenceLaw ν).map
        (Combinatorics.Sequence.blockCoordinates start length)).real
        {block | (past, block) ∈
          tubeBlockPairEvent lower width v₁ v₂ start length} := by
    intro past hpast
    have hpast' : (∑ j : Fin start, past j) ∈
        Set.Icc lower (lower + width) := hgoodTube hpast
    have hbridge :=
      measure_blockCoordinates_finiteTubeEndpoint_eq_relativeHorizontalTubeEndpointWindowEvent
        ν (lower := lower) (width := width) (v₁ := v₁) (v₂ := v₂)
          hpast' start length
    have hbound' := hbound (∑ j : Fin start, past j) hpast
    have hbridgeReal := congrArg ENNReal.toReal hbridge
    change bound ≤ ((iidSequenceLaw ν)
      (relativeHorizontalTubeEndpointWindowEvent
        (lower - ∑ j : Fin start, past j) width length v₁ v₂)).toReal at hbound'
    rw [← hbridgeReal] at hbound'
    change bound ≤ (((iidSequenceLaw ν).map
      (Combinatorics.Sequence.blockCoordinates start length))
        {block | (past, block) ∈
          tubeBlockPairEvent lower width v₁ v₂ start length}).toReal
    simpa only [tubeBlockPairEvent, Set.mem_ofPred_eq] using hbound'
  have hblocks := indepFun_blockCoordinates_blockCoordinates ν 0 start length
  have hnext : Measurable
      (Combinatorics.Sequence.blockCoordinates (E := ℝ) (0 + start) length) := by
    simpa only [Nat.zero_add] using
      (measurable_blockCoordinates (E := ℝ) start length)
  have hconditional := hblocks.condExp_indicator_pairEvent_ae_eq_sectionProbability
    (measurable_blockCoordinates (E := ℝ) 0 start)
    hnext
    (tubeBlockPairEvent lower width v₁ v₂ start length)
    (measurableSet_tubeBlockPairEvent lower width v₁ v₂ start length)
  have hconditional' := by
    simpa only [Nat.zero_add] using hconditional
  filter_upwards [hconditional'] with increment hconditional
  intro hgood
  rw [hconditional]
  exact hsections (Combinatorics.Sequence.blockCoordinates 0 start increment) hgood

/-- The block-start conditional probability bound in the natural domain
filtration, using the translated zero-start bound from the preceding theorem. -/
private lemma iidSequenceLaw_condExp_tubeBlockEvent_ge
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (lower width v₁ v₂ : ℝ) (start length : ℕ)
    (good : Set ℝ)
    (hgoodTube : good ⊆ Set.Icc lower (lower + width))
    {bound : ℝ}
    (hbound : ∀ initial ∈ good,
      bound ≤ (iidSequenceLaw ν).real
        (relativeHorizontalTubeEndpointWindowEvent
          (lower - initial) width length v₁ v₂)) :
    ∀ᵐ increment ∂iidSequenceLaw ν,
      (∑ j : Fin start,
          Combinatorics.Sequence.blockCoordinates 0 start increment j) ∈
        good →
      bound ≤ condExp (sequencePrefixFiltration (E := ℝ) start)
        (iidSequenceLaw ν)
        ((tubeBlockEvent start length lower width v₁ v₂).indicator
          (fun _ => (1 : ℝ))) increment := by
  rw [sequencePrefixFiltration_eq_comap_blockCoordinates]
  have hconditional := iidSequenceLaw_condExp_tubeBlockPairEvent_ge
    ν lower width v₁ v₂ start length good hgoodTube hbound
  have hindicator :
      (tubeBlockEvent start length lower width v₁ v₂).indicator
          (fun _ => (1 : ℝ)) =
        fun increment =>
          (tubeBlockPairEvent lower width v₁ v₂ start length).indicator
            (fun _ => (1 : ℝ))
            (Combinatorics.Sequence.blockCoordinates 0 start increment,
              Combinatorics.Sequence.blockCoordinates start length increment) := by
    funext increment
    rfl
  rw [hindicator]
  exact hconditional

/-- Successive horizontal tube blocks multiply their conditional lower
bounds when each successful prefix enters the next tube. -/
lemma measureReal_tubeBlockIntersection_ge_prod
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

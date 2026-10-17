/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Probability.Process.Filtration.ConditionalBlocks
public import Probability.Sequence.IID.Basic
public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Event
public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.JumpPattern.Basic
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Lemmas.JumpPattern.Geometry
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Lemmas.JumpPattern.Probability
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Lemmas.JumpPattern.Setup

/-!
# Finite union bound over jump patterns

The proof-specific declarations are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.measureReal_noLargeDropEvent_le_sum_jumpPatternProducts_of_uniformBlockBound`:
  the no-large-drop event probability is bounded by the sum of fixed-pattern
  block products over admissible patterns, given a uniform block bound.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.measureReal_noLargeDropEvent_le_jumpPatternCount_mul_pow_of_sumBound`:
  bounding the number of admissible patterns and each product by
  $2^q p^{q-K}$ gives the finite jump-pattern estimate.

These steps follow Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.3.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

lemma measureReal_noLargeDropEvent_le_sum_jumpPatternProducts_of_uniformBlockBound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {v d tubeWidth₀ : ℝ}
    (horizon blockLength : ℕ)
    (hpatternBound : ∀ tubeWidth : ℝ, tubeWidth₀ ≤ tubeWidth →
      ∀ upper binWidth : ℝ, ∀ pattern : Finset (Fin (horizon / blockLength)),
        (iidSequenceLaw ν).real
          (ProbabilityTheory.conditionalBlockIntersection
            (drawdownJumpPatternTubeEvent (horizon % blockLength) blockLength pattern
              upper binWidth tubeWidth) (horizon / blockLength)) ≤
          ∏ j ∈ Finset.range (horizon / blockLength),
            drawdownJumpPatternBound pattern
              (Real.exp (tubeWidth ^ v -
                d * ((blockLength : ℝ) / tubeWidth ^ 2))) j)
    (delta threshold binWidth : ℝ) (hbinWidth : 0 < binWidth)
    (htubeWidth : tubeWidth₀ ≤ binWidth + delta) :
      (iidSequenceLaw ν).real
        (noLargeDropEndpointBelowEvent horizon delta threshold) ≤
        ∑ pattern ∈ drawdownAdmissibleJumpPatterns
            (horizon / blockLength)
            (⌊(threshold + delta) / binWidth⌋₊ + 1),
          ∏ j ∈ Finset.range (horizon / blockLength),
            drawdownJumpPatternBound pattern
              (Real.exp ((binWidth + delta) ^ v -
                d * ((blockLength : ℝ) / (binWidth + delta) ^ 2))) j := by
  let tubeWidth := binWidth + delta
  let q := horizon / blockLength
  let maxJumps := ⌊(threshold + delta) / binWidth⌋₊ + 1
  let patterns := drawdownAdmissibleJumpPatterns q maxJumps
  let events : Finset (Fin q) → Set (ℕ → ℝ) := fun pattern =>
    drawdownJumpPatternTubeIntersection (horizon % blockLength) blockLength
      pattern (threshold + delta) binWidth tubeWidth
  have hsubset : noLargeDropEndpointBelowEvent horizon delta threshold ⊆
      ⋃ pattern ∈ patterns, events pattern := by
    intro increment hevent
    have hmem := drawdown_noLargeDropEvent_subset_jumpPatternUnion
      increment horizon blockLength delta threshold binWidth hbinWidth hevent
    simpa [q, maxJumps, patterns, events] using hmem
  have hbound : ∀ pattern ∈ patterns,
      (iidSequenceLaw ν).real (events pattern) ≤
        ∏ j ∈ Finset.range q,
          drawdownJumpPatternBound pattern
            (Real.exp (tubeWidth ^ v -
              d * ((blockLength : ℝ) / tubeWidth ^ 2))) j := by
    intro pattern hpattern
    simpa [events, q, drawdownJumpPatternTubeIntersection] using
      hpatternBound tubeWidth htubeWidth (threshold + delta) binWidth pattern
  have hfiniteUnion : (iidSequenceLaw ν) (⋃ pattern ∈ patterns, events pattern) ≠ ∞ :=
    measure_ne_top (iidSequenceLaw ν) _
  calc
    (iidSequenceLaw ν).real
        (noLargeDropEndpointBelowEvent horizon delta threshold) ≤
        (iidSequenceLaw ν).real (⋃ pattern ∈ patterns, events pattern) :=
      measureReal_mono hsubset hfiniteUnion
    _ ≤ ∑ pattern ∈ patterns, (iidSequenceLaw ν).real (events pattern) :=
      measureReal_biUnion_finset_le patterns events
    _ ≤ ∑ pattern ∈ patterns,
          ∏ j ∈ Finset.range q,
            drawdownJumpPatternBound pattern
              (Real.exp (tubeWidth ^ v -
                d * ((blockLength : ℝ) / tubeWidth ^ 2))) j := by
      exact Finset.sum_le_sum hbound

/-- Counting the admissible jump patterns and using at least `q-K` nonjump
blocks gives the exponential-count times one-block-power estimate from the
proof of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.3. -/
lemma measureReal_noLargeDropEvent_le_jumpPatternCount_mul_pow_of_sumBound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {v d : ℝ}
    (horizon blockLength : ℕ)
    (delta threshold binWidth : ℝ)
    (hsum : (iidSequenceLaw ν).real
      (noLargeDropEndpointBelowEvent horizon delta threshold) ≤
      ∑ pattern ∈ drawdownAdmissibleJumpPatterns
          (horizon / blockLength)
          (⌊(threshold + delta) / binWidth⌋₊ + 1),
        ∏ j ∈ Finset.range (horizon / blockLength),
          drawdownJumpPatternBound pattern
            (Real.exp ((binWidth + delta) ^ v -
              d * ((blockLength : ℝ) / (binWidth + delta) ^ 2))) j)
    (hp : Real.exp ((binWidth + delta) ^ v -
      d * ((blockLength : ℝ) / (binWidth + delta) ^ 2)) ≤ 1) :
    (iidSequenceLaw ν).real
        (noLargeDropEndpointBelowEvent horizon delta threshold) ≤
      (2 : ℝ) ^ (horizon / blockLength) *
        Real.exp ((binWidth + delta) ^ v -
          d * ((blockLength : ℝ) / (binWidth + delta) ^ 2)) ^
            (horizon / blockLength -
              (⌊(threshold + delta) / binWidth⌋₊ + 1)) := by
  let q := horizon / blockLength
  let maxJumps := ⌊(threshold + delta) / binWidth⌋₊ + 1
  let patterns := drawdownAdmissibleJumpPatterns q maxJumps
  let p := Real.exp ((binWidth + delta) ^ v -
    d * ((blockLength : ℝ) / (binWidth + delta) ^ 2))
  have hpatternProduct : ∀ pattern ∈ patterns,
      (∏ j ∈ Finset.range q, drawdownJumpPatternBound pattern p j) ≤
        p ^ (q - maxJumps) := by
    intro pattern hpattern
    have hcard : pattern.card ≤ maxJumps := by
      simpa [patterns, drawdownAdmissibleJumpPatterns, q, maxJumps] using hpattern
    exact drawdown_prod_jumpPatternBound_le_pow pattern p
      (Real.exp_nonneg _) hp hcard
  have hsum' : (iidSequenceLaw ν).real
      (noLargeDropEndpointBelowEvent horizon delta threshold) ≤
      ∑ pattern ∈ patterns,
        ∏ j ∈ Finset.range q, drawdownJumpPatternBound pattern p j := by
    simpa [q, maxJumps, patterns, p] using hsum
  have hcardPatterns : patterns.card ≤ 2 ^ q := by
    calc
      patterns.card ≤ Finset.univ.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 ^ q := by simp [q]
  have hsumPow :
      (∑ pattern ∈ patterns,
        ∏ j ∈ Finset.range q, drawdownJumpPatternBound pattern p j) ≤
          (patterns.card : ℝ) * p ^ (q - maxJumps) := by
    calc
      (∑ pattern ∈ patterns,
          ∏ j ∈ Finset.range q, drawdownJumpPatternBound pattern p j) ≤
          ∑ pattern ∈ patterns, p ^ (q - maxJumps) :=
        Finset.sum_le_sum hpatternProduct
      _ = (patterns.card : ℝ) * p ^ (q - maxJumps) := by simp
  have hcount : (patterns.card : ℝ) ≤ (2 : ℝ) ^ q := by
    exact_mod_cast hcardPatterns
  have hpowerNonneg : 0 ≤ p ^ (q - maxJumps) :=
    pow_nonneg (Real.exp_nonneg _) _
  have hfinal := hsum'.trans hsumPow
  have hfinal' := hfinal.trans
    (mul_le_mul_of_nonneg_right hcount hpowerNonneg)
  simpa [q, maxJumps, p, mul_comm] using hfinal'

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end

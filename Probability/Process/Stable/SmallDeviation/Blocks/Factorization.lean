/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Mathlib.Probability.Independence.Basic
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Basic
public import Probability.Process.Stable.Levy
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Events
import Probability.Process.Stable.FiniteDimensional
import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Stationarity
import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Independence
import MeasureTheory.Measure.Algebra.FiniteProduct

/-!
# Probability factorization across stable-process blocks

The stopped prefix path is independent of the next translated block. This
supports an induction over the number of blocks in the tube event.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- All information in the stopped prefix path is independent of the entire
next translated block path. -/
theorem IsStableLevyProcess.indepFun_rationalPrefix_nextBlock
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (j : Fin blocks) :
    (rationalUniformPrefixPath X blocks j.val hblocks) ⟂ᵢ[P]
      (fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) := by
  exact h.increments.indepIncrements.indepFun_rationalPrefix_nextBlock
    (fun t => h.increments.aemeasurable_eval t) blocks hblocks j

/-- The event for all previous block tubes factors from the next block tube.
This gives the exact induction step for the multi-block probability product. -/
theorem IsStableLevyProcess.measure_prefixTube_inter_nextBlock
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (j : Fin blocks) (width : ℝ) :
    P (rationalUniformPrefixTubeEvent X width hblocks j.val ∩
        rationalUniformBlockTubeEvent X width hblocks j) =
      P (rationalUniformPrefixTubeEvent X width hblocks j.val) *
        P (rationalUniformBlockTubeEvent X width hblocks j) := by
  have hindep := h.indepFun_rationalPrefix_nextBlock blocks hblocks j
  have hfactor := hindep.measure_inter_preimage_eq_mul
    (rationalUniformPrefixTubeSet width hblocks j.val)
    (Skorokhod.rationalCoordinateOscillationTube width)
    (measurableSet_rationalUniformPrefixTubeSet width hblocks j.val)
    (Skorokhod.measurableSet_rationalCoordinateOscillationTube width)
  simpa [rationalUniformPrefixTubeEvent_eq_preimage, rationalUniformBlockTubeEvent]
    using hfactor

/-- A common measurable condition on each of finitely many translated block
paths has probability at least the corresponding power of its first-block
probability. This is the non-adaptive finite-block product bound. -/
theorem IsStableLevyProcess.pow_le_measure_rationalUniformPrefixBlockEvent
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (V : Set (↑RationalCoordinate.UnitInterval → ℝ))
    (hV : MeasurableSet V) (q : ENNReal)
    (hq : q ≤ P ((fun ω s => rationalUniformBlockProcessFromTime X hblocks
      ⟨0, hblocks⟩ s ω) ⁻¹' V)) :
    q ^ blocks ≤ P (rationalUniformPrefixBlockEvent X V hblocks blocks) := by
  let nextEvent : ℕ → Set Ω := fun m =>
    if hm : m < blocks then
      (fun ω s => rationalUniformBlockProcessFromTime X hblocks
        ⟨m, hm⟩ s ω) ⁻¹' V
    else Set.univ
  have hzero : rationalUniformPrefixBlockEvent X V hblocks 0 = Set.univ :=
    rationalUniformPrefixBlockEvent_zero X V hblocks
  have hrec : ∀ m < blocks,
      rationalUniformPrefixBlockEvent X V hblocks (m + 1) =
        rationalUniformPrefixBlockEvent X V hblocks m ∩ nextEvent m := by
    intro m hm
    simpa [nextEvent, hm] using
      (rationalUniformPrefixBlockEvent_succ X V hblocks m hm)
  have hfactor : ∀ m < blocks,
      P (rationalUniformPrefixBlockEvent X V hblocks m ∩ nextEvent m) =
        P (rationalUniformPrefixBlockEvent X V hblocks m) * P (nextEvent m) := by
    intro m hm
    let j : Fin blocks := ⟨m, hm⟩
    have hindep := h.indepFun_rationalPrefix_nextBlock blocks hblocks j
    have hfactor' := hindep.measure_inter_preimage_eq_mul
      (rationalUniformPrefixBlockSet hblocks m V) V
      (measurableSet_rationalUniformPrefixBlockSet hblocks m hV) hV
    simpa [nextEvent, hm, j, rationalUniformPrefixBlockEvent_eq_preimage] using hfactor'
  have hprob : ∀ m < blocks, q ≤ P (nextEvent m) := by
    intro m hm
    let j : Fin blocks := ⟨m, hm⟩
    have hqj : q ≤ P ((fun ω s =>
        rationalUniformBlockProcessFromTime X hblocks j s ω) ⁻¹' V) := by
      rw [(h.increments.indepIncrements.rationalUniformBlockProcess_identDistrib
        h.toIsLevyProcess.stationaryIncrements blocks hblocks j
        ⟨0, hblocks⟩).measure_mem_eq hV]
      exact hq
    simpa [nextEvent, hm, j] using hqj
  have hbound := MeasureTheory.mul_pow_le_measure_prefix_inter_of_factorization
    (μ := P) (rationalUniformPrefixBlockEvent X V hblocks) nextEvent q blocks
    hrec hfactor hprob
  have hstart : P (rationalUniformPrefixBlockEvent X V hblocks 0) = 1 := by
    rw [hzero]
    simp
  simpa [hstart] using hbound

end ProbabilityTheory

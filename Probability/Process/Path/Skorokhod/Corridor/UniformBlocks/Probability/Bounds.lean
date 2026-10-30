/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Events
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.Probability.IdentDistrib
public import Probability.Process.StationaryIncrements.Basic
import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Probability.Independence
import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Probability.Stationarity
import Algebra.Order.Monoid.Recurrence

/-!
# Probability bounds for uniform block restrictions

## Public declarations

This module contains the measure-theoretic consequences of the generic
uniform-block construction.  It assumes only a measure on the sample space,
independence of the block paths, and equality of their laws; stable-process
instances are supplied by the Stable small-deviation adapters.

* `measure_rationalTube_le_pow_of_iIndep_uniformBlocks` states
  `P(X ∈ rationalCoordinateOscillationTube width) ≤
  (P(block 0 ∈ rationalCoordinateOscillationTube width)) ^ blocks`, assuming
  independence and a common law for the block paths.
* `measure_rationalTube_le_uniformBlockInter` bounds the global tube
  probability by the intersection of all block tube probabilities.
* `HasIndepIncrements.pow_le_measure_rationalUniformPrefixBlockEvent` gives
  `q ^ blocks ≤ P(⋂ j, (fun ω s => rationalUniformBlockProcessFromTime
  X hblocks j s ω) ⁻¹' V)` from stationary independent increments and
  one-block probability at least `q`.
-/

open MeasureTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

/-- If each translated block has the same measurable success condition and
the first block succeeds with probability at least `q`, then the probability
that all blocks succeed is at least `q ^ blocks`. Independent increments
factor the successive block events; stationary increments transfer the
first-block bound to every block. -/
theorem HasIndepIncrements.pow_le_measure_rationalUniformPrefixBlockEvent
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : HasIndepIncrements X P)
    (hstationary : HasStationaryIncrements X P)
    (hXmeas : ∀ t : ℝ≥0, AEMeasurable (fun ω => X t ω) P)
    (blocks : ℕ) (hblocks : 0 < blocks)
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
    have hindep := h.indepFun_rationalPrefix_nextBlock hXmeas blocks hblocks j
    have hfactor' := hindep.measure_inter_preimage_eq_mul
      (rationalUniformPrefixBlockSet hblocks m V) V
      (measurableSet_rationalUniformPrefixBlockSet hblocks m hV) hV
    simpa [nextEvent, hm, j, rationalUniformPrefixBlockEvent_eq_preimage] using hfactor'
  have hprob : ∀ m < blocks, q ≤ P (nextEvent m) := by
    intro m hm
    let j : Fin blocks := ⟨m, hm⟩
    have hqj : q ≤ P ((fun ω s =>
        rationalUniformBlockProcessFromTime X hblocks j s ω) ⁻¹' V) := by
      rw [(h.rationalUniformBlockProcess_identDistrib
        hstationary blocks hblocks j ⟨0, hblocks⟩).measure_mem_eq hV]
      exact hq
    simpa [nextEvent, hm, j] using hqj
  have hstart : P (rationalUniformPrefixBlockEvent X V hblocks 0) = 1 := by
    rw [hzero]
    simp
  have hstep : ∀ m < blocks,
      q * P (rationalUniformPrefixBlockEvent X V hblocks m) ≤
        P (rationalUniformPrefixBlockEvent X V hblocks (m + 1)) := by
    intro m hm
    calc
      q * P (rationalUniformPrefixBlockEvent X V hblocks m) =
          P (rationalUniformPrefixBlockEvent X V hblocks m) * q := by
        rw [mul_comm]
      _ ≤ P (rationalUniformPrefixBlockEvent X V hblocks m) * P (nextEvent m) :=
        mul_le_mul_of_nonneg_left (hprob m hm) zero_le
      _ = P (rationalUniformPrefixBlockEvent X V hblocks m ∩ nextEvent m) :=
        (hfactor m hm).symm
      _ = P (rationalUniformPrefixBlockEvent X V hblocks (m + 1)) := by
        rw [← hrec m hm]
  have hstart' : 1 ≤ P (rationalUniformPrefixBlockEvent X V hblocks 0) := by
    rw [hstart]
  exact IsOrderedMonoid.pow_le_of_mul_le_succ
    (fun m => P (rationalUniformPrefixBlockEvent X V hblocks m))
    blocks q hstart' hstep

/-- For any measure on rational-coordinate paths, the global tube probability
is bounded by the probability of the intersection of its block restrictions.
This theorem is purely pathwise; independent increments are needed for the
product formula below. -/
theorem measure_rationalTube_le_uniformBlockInter
    (P : Measure (↑RationalCoordinate.UnitInterval → ℝ)) (width : ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) :
    P (Skorokhod.rationalCoordinateOscillationTube width) ≤
      P (⋂ j : Fin blocks, rationalTubeBlockEvent width hblocks j) :=
  measure_mono
    (rationalCoordinateOscillationTube_subset_iInter_uniformBlockEvents
      width hblocks)

/-- The upper block inequality for a uniform rational partition, conditional
only on independence of the block paths and equality of their path laws. -/
theorem measure_rationalTube_le_pow_of_iIndep_uniformBlocks
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ↑RationalCoordinate.UnitInterval → Ω → ℝ)
    {blocks : ℕ} (hblocksPos : 0 < blocks) (width : ℝ)
    (hindep : iIndepFun (rationalUniformBlockProcess X hblocksPos) P)
    (hsameLaw : ∀ j : Fin blocks,
      IdentDistrib (rationalUniformBlockProcess X hblocksPos j)
        (rationalUniformBlockProcess X hblocksPos ⟨0, hblocksPos⟩) P P) :
    P ((fun ω q => X q ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width) ≤
      (P ((rationalUniformBlockProcess X hblocksPos ⟨0, hblocksPos⟩) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width)) ^ blocks := by
  let blockProcess := rationalUniformBlockProcess X hblocksPos
  have hsubset :
      (fun ω q => X q ω) ⁻¹'
          Skorokhod.rationalCoordinateOscillationTube width ⊆
        ⋂ j : Fin blocks,
          blockProcess j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width := by
    intro ω hω
    simp only [Set.mem_iInter]
    intro j
    have hglobal : (fun q => X q ω) ∈
        Skorokhod.rationalCoordinateOscillationTube width := hω
    have hlocal :=
      rationalCoordinateOscillationTube_subset_iInter_uniformBlockEvents
        width hblocksPos hglobal
    have hlocalj := Set.mem_iInter.mp hlocal j
    simpa [blockProcess, rationalUniformBlockProcess, rationalTubeBlockEvent,
      Set.mem_preimage] using hlocalj
  have hfactor :
      P (⋂ j : Fin blocks,
        blockProcess j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width) =
        ∏ j : Fin blocks,
          P (blockProcess j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width) := by
    simpa [blockProcess] using hindep.measure_inter_preimage_eq_mul
      (Finset.univ : Finset (Fin blocks))
      (sets := fun _ => Skorokhod.rationalCoordinateOscillationTube width)
      (by
        intro j hj
        exact Skorokhod.measurableSet_rationalCoordinateOscillationTube width)
  have hsame (j : Fin blocks) :
      P (blockProcess j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width) =
        P (blockProcess ⟨0, hblocksPos⟩ ⁻¹'
          Skorokhod.rationalCoordinateOscillationTube width) := by
    exact (hsameLaw j).measure_mem_eq
      (Skorokhod.measurableSet_rationalCoordinateOscillationTube width)
  calc
    P ((fun ω q => X q ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width) ≤
      P (⋂ j : Fin blocks,
        blockProcess j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width) :=
      measure_mono hsubset
    _ = ∏ j : Fin blocks,
        P (blockProcess j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width) :=
      hfactor
    _ = (P (blockProcess ⟨0, hblocksPos⟩ ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width)) ^ blocks := by
      simp_rw [hsame]
      simp


end ProbabilityTheory

end

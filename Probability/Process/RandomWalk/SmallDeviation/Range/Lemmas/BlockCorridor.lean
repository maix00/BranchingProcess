/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Algebra.BigOperators.AdditivePath.Basic
import Combinatorics.Sequence.Block
import Probability.Process.RandomWalk.Path.Block.Oscillation
import Probability.Process.RandomWalk.Path.Block.Partition.Basic
import Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft.Basic
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.FromIncrementLaw.Normal.ContinuousBoundary
import Probability.MeasureTheory.Asymptotics.SmallDeviation
import Topology.Cadlag.Basic
import Topology.Cadlag.Skorokhod.Path.TerminalLeft
import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.ContinuousBoundary
import Topology.Cadlag.Skorokhod.SmallDeviation.PathSets
import Topology.Cadlag.Skorokhod.SmallDeviation.RangeCover

/-!
# Internal block-to-corridor inclusions

These deterministic inclusions convert a finite block oscillation bound into
source-path corridor and range-tube events. They support the public finite-
variance probability bounds in the parent `Range` modules.

## Internal proof declarations

- `blockOscillationEvent_partialSum_abs_le` bounds each partial sum by the
  block width.
- `blockOscillationEvent_subset_enlargedSourceCorridor` embeds the block event
  in an enlarged centered source corridor.
- `blockOscillationEvent_subset_sourceRangeTube` embeds it in the source-path
  range tube used by the finite-cover rate.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Range

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete
open Skorokhod.PathClass.StepCorridor

/-- A block oscillation bound controls every partial sum relative to the
initial value zero. -/
lemma blockOscillationEvent_partialSum_abs_le
    {n : ℕ} (hn : 0 < n) {width : ℝ} (increment : ℕ → ℝ)
    (hosc : blockOscillationEvent width (n - 1)
      (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment))
    (k : Fin n) :
    |AdditivePath.displacement (k : ℕ) increment| ≤ width := by
  have hosc' : Metric.OscillationBounded
      (fun i : Fin ((n - 1) + 1) =>
        Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment) i)
      width := by
    change Metric.OscillationBounded _ width at hosc
    exact hosc
  have h := hosc' 0 (Fin.cast (by omega : n = (n - 1) + 1) k)
  change |Fin.partialSum
      (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment) 0 -
        Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment)
          (Fin.cast (by omega : n = (n - 1) + 1) k)| ≤ width at h
  rw [partialSum_blockCoordinates (start := 0) (increment := increment) 0,
    partialSum_blockCoordinates (start := 0) (increment := increment)
      (Fin.cast (by omega : n = (n - 1) + 1) k)] at h
  simpa [Fin.cast] using h

/-- A block whose oscillation is at most `width` lies in a strict centered
source corridor after enlarging its spatial scale by a factor greater than
two. The source horizon `n` records exactly the sums through time `n - 1`. -/
lemma blockOscillationEvent_subset_enlargedSourceCorridor
    {n : ℕ} (hn : 0 < n) {width factor : ℝ}
    (hwidth : 0 < width) (hfactor : 2 < factor)
    (increment : ℕ → ℝ) :
    blockOscillationEvent width (n - 1)
      (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment) →
    terminalLeftNormalizedStepCadlagPathIcc (fun _ => factor * width) n increment ∈
      relativeContinuousBoundaryCorridorSet
        (ContinuousMap.const unitInterval (-(1 / 2 : ℝ)))
        (ContinuousMap.const unitInterval (1 / 2 : ℝ)) := by
  intro hosc
  let scale : ℕ → ℝ := fun _ => factor * width
  have hscale : 0 < scale n := mul_pos (by linarith) hwidth
  have htube : InOpenHorizontalTube (1 / 2 : ℝ) (scale n) (n - 1) increment := by
    intro k
    let j : Fin n := ⟨k.val + 1, by omega⟩
    have hpartial := blockOscillationEvent_partialSum_abs_le hn increment hosc j
    have hpartial' : |AdditivePath.displacement (k + 1) increment| ≤ width := by
      simpa [j] using hpartial
    have hfactorWidth : width < scale n / 2 := by
      dsimp [scale]
      nlinarith
    have hbounds := abs_le.mp hpartial'
    change -(1 / 2 : ℝ) * scale n < AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment < (1 - 1 / 2 : ℝ) * scale n
    constructor
    · dsimp [scale]
      nlinarith [hbounds.1, hfactorWidth]
    · dsimp [scale]
      nlinarith [hbounds.2, hfactorWidth]
  have hpath : terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
      Skorokhod.rangeInOpenInterval (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    have hequiv := terminalLeftNormalizedStepCadlagPathIcc_mem_rangeInOpenInterval_iff
      scale hn hscale (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num) increment
    convert hequiv.mpr htube using 1; norm_num
  change terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
    Skorokhod.terminalLeftPathSpace ∩
      continuousBoundaryCorridorSet
        (ContinuousMap.const unitInterval (-(1 / 2 : ℝ)))
        (ContinuousMap.const unitInterval (1 / 2 : ℝ))
  refine ⟨Skorokhod.terminalLeftPath_mem_space
    (normalizedStepCadlagPathIcc scale n increment), ?_⟩
  rcases (Skorokhod.mem_rangeInOpenInterval_iff.mp hpath) with
    ⟨margin, hmargin, hinside⟩
  refine ⟨?_, ?_⟩
  · simp [terminalLeftNormalizedStepCadlagPathIcc_apply_of_ne_top,
      normalizedStepPath_zero]
  · intro t
    have ht := hinside t
    change -(1 / 2 : ℝ) <
        terminalLeftNormalizedStepCadlagPathIcc scale n increment t ∧
      terminalLeftNormalizedStepCadlagPathIcc scale n increment t < (1 / 2 : ℝ)
    constructor
    · exact lt_of_lt_of_le (by linarith [hmargin]) ht.1
    · exact lt_of_le_of_lt ht.2 (by linarith [hmargin])

/-- Pairwise oscillation of the block partial sums is the range diameter of
the source-convention step path. -/
lemma blockOscillationEvent_subset_sourceRangeTube
    {n : ℕ} (hn : 0 < n) {width factor : ℝ}
    (hwidth : 0 < width) (hfactor : 1 < factor)
    (scale : ℕ → ℝ) (hscale : scale n = factor * width / 2)
    (increment : ℕ → ℝ)
    (hosc : blockOscillationEvent width (n - 1)
      (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment)) :
    terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
      Skorokhod.rangeTubeStartingAtZero 1 := by
  have hscalePos : 0 < scale n := by rw [hscale]; positivity
  have hoscBlock : Metric.OscillationBounded
      (fun i : Fin ((n - 1) + 1) =>
        Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment) i)
      width := by
    change Metric.OscillationBounded _ width at hosc
    exact hosc
  have hdisplacement (i j : Fin n) :
      |AdditivePath.displacement (i : ℕ) increment -
          AdditivePath.displacement (j : ℕ) increment| ≤ width := by
    have h := hoscBlock
      (Fin.cast (by omega : n = (n - 1) + 1) i)
      (Fin.cast (by omega : n = (n - 1) + 1) j)
    change |Fin.partialSum
        (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment)
          (Fin.cast (by omega : n = (n - 1) + 1) i) -
      Fin.partialSum
        (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment)
          (Fin.cast (by omega : n = (n - 1) + 1) j)| ≤ width at h
    rw [partialSum_blockCoordinates (start := 0) (increment := increment)
          (Fin.cast (by omega : n = (n - 1) + 1) i),
      partialSum_blockCoordinates (start := 0) (increment := increment)
          (Fin.cast (by omega : n = (n - 1) + 1) j)] at h
    simpa [Fin.cast] using h
  have hrange := terminalLeftNormalizedStepCadlagPathIcc_range_eq_scaledDisplacement
    scale hn increment
  let path := terminalLeftNormalizedStepCadlagPathIcc scale n increment
  have hpathStart : path ⊥ = 0 := by
    change terminalLeftNormalizedStepCadlagPathIcc scale n increment ⊥ = 0
    rw [terminalLeftNormalizedStepCadlagPathIcc_apply_of_ne_top
      scale n increment (t := ⊥) (by norm_num [unitInterval])]
    simp [normalizedStepPath, AdditivePath.displacement]
  have hRange : Set.range path =
      Set.range (fun k : Fin n => (scale n)⁻¹ *
        AdditivePath.displacement (k : ℕ) increment) := by
    simpa [path] using hrange
  have hpathOsc : Metric.OscillationBounded path (width / scale n) := by
    intro s t
    have hs : path s ∈ Set.range path := ⟨s, rfl⟩
    have ht : path t ∈ Set.range path := ⟨t, rfl⟩
    rw [hRange] at hs ht
    rcases hs with ⟨i, hi⟩
    rcases ht with ⟨j, hj⟩
    rw [← hi, ← hj]
    have hdiff := hdisplacement i j
    change |(scale n)⁻¹ * AdditivePath.displacement (i : ℕ) increment -
        (scale n)⁻¹ * AdditivePath.displacement (j : ℕ) increment| ≤ width / scale n
    rw [show (scale n)⁻¹ * AdditivePath.displacement (i : ℕ) increment -
        (scale n)⁻¹ * AdditivePath.displacement (j : ℕ) increment =
          (scale n)⁻¹ * (AdditivePath.displacement (i : ℕ) increment -
            AdditivePath.displacement (j : ℕ) increment) by ring,
      abs_mul, abs_of_nonneg (inv_nonneg.mpr hscalePos.le)]
    calc
      (scale n)⁻¹ * |AdditivePath.displacement (i : ℕ) increment -
          AdditivePath.displacement (j : ℕ) increment| ≤ (scale n)⁻¹ * width :=
        mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hscalePos.le)
      _ = width / scale n := by rw [div_eq_mul_inv]; ring
  have hwidthScale : width / scale n = 2 / factor := by
    rw [hscale]
    field_simp [ne_of_gt hfactor, ne_of_gt hwidth]
  have hstrict : width / scale n < 2 := by
    rw [hwidthScale]
    exact (div_lt_iff₀ (by linarith : 0 < factor)).2 (by nlinarith)
  change path ⊥ = 0 ∧ path ∈ Skorokhod.oscillationInOpenTube (2 * 1)
  refine ⟨hpathStart, ?_⟩
  refine ⟨2 - width / scale n, sub_pos.mpr hstrict, ?_⟩
  simpa using hpathOsc


end ProbabilityTheory.RandomWalk.SmallDeviation.Range

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Basic
public import Probability.Sequence.Block
public import Probability.Sequence.IID.Basic
public import Probability.Process.RandomWalk.Path.Window.Core
import Probability.Sequence.IID.Blocks.StoppingTime

/-!
# IID laws of finite interval path events

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.iidSequenceLaw_map_blockCoordinates_finiteInterval_le`:
  a bound for an IID random walk to stay in a closed interval transfers to the
  law of its finite increment block, provided the initial position belongs to
  that interval.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- The law of a finite coordinate block assigns at most the corresponding
infinite-walk probability to the finite-path interval event. -/
lemma iidSequenceLaw_map_blockCoordinates_finiteInterval_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {length : ℕ} {lower upper : ℝ}
    (hzero : (0 : ℝ) ∈ Set.Icc lower upper)
    {bound : ℝ≥0∞}
    (hbound : iidSequenceLaw ν
      {increment : ℕ → ℝ | ∀ j : Fin length,
        AdditivePath.displacement (j + 1) increment ∈ Set.Icc lower upper} ≤
      bound) :
    ((iidSequenceLaw ν).map
      (Combinatorics.Sequence.blockCoordinates 0 length))
      {block | FiniteInClosedInterval lower upper 0 block} ≤ bound := by
  have hfinite : MeasurableSet
      {block : Fin length → ℝ | FiniteInClosedInterval lower upper 0 block} :=
    measurableSet_finiteInClosedInterval lower upper 0 length
  have hevent :
      {increment : ℕ → ℝ |
        FiniteInClosedInterval lower upper 0
          (Combinatorics.Sequence.blockCoordinates 0 length increment)} =
      {increment | ∀ j : Fin length,
        AdditivePath.displacement (j + 1) increment ∈ Set.Icc lower upper} := by
    ext increment
    have hbridge := finiteInClosedInterval_blockCoordinates_iff
      lower upper 0 0 length increment
    have hstays := staysIn_Icc_iff_inClosedInterval
      lower upper length 0 hzero (fun k => increment (0 + k))
    constructor
    · intro h
      have hpath := hbridge.mp h
      have hstay := hstays.mpr hpath
      simpa [StaysIn, Nat.zero_add] using hstay
    · intro h
      have hstay : StaysIn (Set.Icc lower upper) length 0
          (fun k => increment (0 + k)) := by
        simpa [StaysIn, Nat.zero_add] using h
      exact hbridge.mpr (hstays.mp hstay)
  calc
    _ = iidSequenceLaw ν
        {increment : ℕ → ℝ | FiniteInClosedInterval lower upper 0
          (Combinatorics.Sequence.blockCoordinates 0 length increment)} := by
      rw [Measure.map_apply (measurable_blockCoordinates 0 length) hfinite]
      rfl
    _ = iidSequenceLaw ν
        {increment : ℕ → ℝ |
          ∀ j : Fin length,
            AdditivePath.displacement (j + 1) increment ∈ Set.Icc lower upper} := by
      rw [hevent]
    _ ≤ bound := hbound

end ProbabilityTheory.RandomWalk

end

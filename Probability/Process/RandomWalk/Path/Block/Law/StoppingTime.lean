/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Filtration
public import Probability.Process.RandomWalk.Path.Block.Law.Excursions
public import Mathlib.Probability.Process.Stopping

/-!
# Excursions after a discrete stopping time

For an IID increment path, a fixed finite block after a stopping time has the
same excursion bound as a deterministic block. The proof splits according to
the stopping-time value and uses independence of each future coordinate block
from the already observed increment prefix.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- A finite-prefix excursion beginning at the random time `τ`. Infinite
stopping times contribute no event. -/
def blockPrefixExceedanceAfter
    (τ : (ℕ → ℝ) → WithTop ℕ) (length : ℕ) (threshold : ℝ) : Set (ℕ → ℝ) :=
  ⋃ n : ℕ, {path | τ path = n} ∩
    blockPrefixExceedance n length threshold

/-- The random walk's fresh-excursion event is the generic finite-coordinate
block event specialized to its measurable partial-sum event. -/
theorem blockPrefixExceedanceAfter_eq_iidBlockEventAfter
    (τ : (ℕ → ℝ) → WithTop ℕ) (length : ℕ) (threshold : ℝ) :
    blockPrefixExceedanceAfter τ length threshold =
      iidBlockEventAfter τ (blockPrefixExceedanceOnCoordinates length threshold) := by
  ext path
  simp only [blockPrefixExceedanceAfter, iidBlockEventAfter,
    Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨n, hτ, hevent⟩
    refine ⟨n, hτ, ?_⟩
    exact (Set.ext_iff.mp
      (blockPrefixExceedance_eq_preimage_blockCoordinates n length threshold).symm
      path).mp hevent
  · rintro ⟨n, hτ, hevent⟩
    refine ⟨n, hτ, ?_⟩
    exact (Set.ext_iff.mp
      (blockPrefixExceedance_eq_preimage_blockCoordinates n length threshold)
      path).mp hevent

theorem measurableSet_blockPrefixExceedance
    (start length : ℕ) (threshold : ℝ) :
    MeasurableSet (blockPrefixExceedance start length threshold) := by
  rw [← blockPrefixExceedance_eq_preimage_blockCoordinates]
  exact (measurableSet_blockPrefixExceedanceOnCoordinates length threshold).preimage
    (measurable_blockCoordinates start length)

/-- At every deterministic time `n`, the stopping-time cell intersected with
the excursion of the next `length` increments factors into its past and
future probabilities. -/
theorem measure_stoppingTimeCell_inter_blockPrefixExceedance_eq_mul
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (τ : (ℕ → ℝ) → WithTop ℕ)
    (hτ : IsStoppingTime (sequencePrefixFiltration (E := ℝ)) τ)
    (n length : ℕ) (threshold : ℝ) :
    (iidSequenceLaw ν)
        ({path | τ path = n} ∩ blockPrefixExceedance n length threshold) =
      (iidSequenceLaw ν) {path | τ path = n} *
        (iidSequenceLaw ν) (blockPrefixExceedance n length threshold) := by
  rw [← blockPrefixExceedance_eq_preimage_blockCoordinates n length threshold]
  have hfactor := iidSequenceLaw_measure_stoppingTimeCell_inter_blockEvent_eq_mul
    ν τ hτ n length (blockPrefixExceedanceOnCoordinates length threshold)
    (measurableSet_blockPrefixExceedanceOnCoordinates length threshold)
  have hshift :
      (iidSequenceLaw ν)
          (Combinatorics.Sequence.blockCoordinates n length ⁻¹'
            blockPrefixExceedanceOnCoordinates length threshold) =
        (iidSequenceLaw ν)
          (Combinatorics.Sequence.blockCoordinates 0 length ⁻¹'
            blockPrefixExceedanceOnCoordinates length threshold) := by
    calc
      _ = ((iidSequenceLaw ν).map
          (Combinatorics.Sequence.blockCoordinates n length))
            (blockPrefixExceedanceOnCoordinates length threshold) :=
        (Measure.map_apply (μ := iidSequenceLaw ν)
          (measurable_blockCoordinates n length)
          (measurableSet_blockPrefixExceedanceOnCoordinates length threshold)).symm
      _ = ((iidSequenceLaw ν).map
          (Combinatorics.Sequence.blockCoordinates 0 length))
            (blockPrefixExceedanceOnCoordinates length threshold) :=
        congrArg (fun μ : Measure (Fin length → ℝ) =>
          μ (blockPrefixExceedanceOnCoordinates length threshold))
          (iidSequenceLaw_map_blockCoordinates ν n length)
      _ = _ := Measure.map_apply (μ := iidSequenceLaw ν)
        (measurable_blockCoordinates 0 length)
        (measurableSet_blockPrefixExceedanceOnCoordinates length threshold)
  calc
    _ = (iidSequenceLaw ν) {path | τ path = n} *
        (iidSequenceLaw ν)
          (Combinatorics.Sequence.blockCoordinates 0 length ⁻¹'
            blockPrefixExceedanceOnCoordinates length threshold) := hfactor
    _ = (iidSequenceLaw ν) {path | τ path = n} *
        (iidSequenceLaw ν)
          (Combinatorics.Sequence.blockCoordinates n length ⁻¹'
            blockPrefixExceedanceOnCoordinates length threshold) := by
          rw [hshift.symm]

/-- A bounded excursion immediately after any discrete stopping time has
probability at most the corresponding deterministic block probability. -/
theorem measure_blockPrefixExceedanceAfter_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (τ : (ℕ → ℝ) → WithTop ℕ)
    (hτ : IsStoppingTime (sequencePrefixFiltration (E := ℝ)) τ)
    (length : ℕ) (threshold : ℝ) :
    (iidSequenceLaw ν) (blockPrefixExceedanceAfter τ length threshold) ≤
      (iidSequenceLaw ν) (blockPrefixExceedance 0 length threshold) := by
  rw [blockPrefixExceedanceAfter_eq_iidBlockEventAfter,
    ← blockPrefixExceedance_eq_preimage_blockCoordinates 0 length threshold]
  exact iidSequenceLaw_measure_iidBlockEventAfter_le
    ν τ hτ length (blockPrefixExceedanceOnCoordinates length threshold)
    (measurableSet_blockPrefixExceedanceOnCoordinates length threshold)

end ProbabilityTheory.RandomWalk

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Rademacher.LastSignChange
public import Probability.Sequence.IID.PrefixBlock
public import Probability.Process.RandomWalk.Path.Filtration

/-!
# Prefix and terminal-block independence for the simple symmetric walk

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.measurableSet_rademacher_positiveCrossing_prefix`:
  $\{S_{m-1}<0,S_m=0\}$ is measurable from the first $m$ increments.
- `ProbabilityTheory.RandomWalk.measurableSet_rademacher_negativeCrossing_prefix`:
  $\{S_{m-1}>0,S_m=0\}$ is measurable from the first $m$ increments.
- `ProbabilityTheory.RandomWalk.measure_rademacher_positiveCrossing_inter_block_eq_mul`:
  for any measurable event $A$ of the next $r$ Boolean increments,
  $\mathbb P(S_{m-1}<0,S_m=0,B_{m,r}\in A)
   =\mathbb P(S_{m-1}<0,S_m=0)\mathbb P(B_{0,r}\in A)$.
- `ProbabilityTheory.RandomWalk.measure_rademacher_negativeCrossing_inter_block_eq_mul`:
  the analogous identity for $S_{m-1}>0$.

These are the prefix/suffix independence steps behind the final
simple-symmetric-walk argument on page 484 of Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned to
stay positive*, Ann. Probab. 4(3) (1976), 480--485.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

private theorem rademacher_displacement_measurable_prefix
    {k start : ℕ} (hkn : k ≤ start) :
    Measurable[sequencePrefixFiltration (E := Bool) start]
      (fun branch : ℕ → Bool =>
        AdditivePath.displacement k (rademacherIncrementPath branch)) := by
  unfold AdditivePath.displacement
  apply Finset.measurable_sum
  intro i hi
  exact measurable_rademacherOfBool.comp
    (sequenceCoordinate_measurable start
      ⟨i, lt_of_lt_of_le (Finset.mem_range.mp hi) hkn⟩)

/-- A negative-to-zero crossing is determined by the increment prefix
through its terminal time. -/
theorem measurableSet_rademacher_positiveCrossing_prefix
    {start : ℕ} (hstart : 0 < start) :
    MeasurableSet[sequencePrefixFiltration (E := Bool) start]
      {branch : ℕ → Bool |
        AdditivePath.displacement (start - 1)
          (rademacherIncrementPath branch) < 0 ∧
        AdditivePath.displacement start
          (rademacherIncrementPath branch) = 0} := by
  exact (measurableSet_Iio.preimage
    (rademacher_displacement_measurable_prefix (by omega))).inter
    ((measurableSet_singleton (0 : ℝ)).preimage
      (rademacher_displacement_measurable_prefix le_rfl))

/-- A positive-to-zero crossing is likewise determined by the prefix. -/
theorem measurableSet_rademacher_negativeCrossing_prefix
    {start : ℕ} (hstart : 0 < start) :
    MeasurableSet[sequencePrefixFiltration (E := Bool) start]
      {branch : ℕ → Bool |
        0 < AdditivePath.displacement (start - 1)
          (rademacherIncrementPath branch) ∧
        AdditivePath.displacement start
          (rademacherIncrementPath branch) = 0} := by
  exact (measurableSet_Ioi.preimage
    (rademacher_displacement_measurable_prefix (by omega))).inter
    ((measurableSet_singleton (0 : ℝ)).preimage
      (rademacher_displacement_measurable_prefix le_rfl))

/-- A negative-to-zero prefix crossing is independent of every
measurable event of the following IID Boolean block. -/
theorem measure_rademacher_positiveCrossing_inter_block_eq_mul
    (start length : ℕ) (hstart : 0 < start)
    (event : Set (Fin length → Bool)) (hevent : MeasurableSet event) :
    (iidSequenceLaw fairBoolMeasure)
        ({branch : ℕ → Bool |
          AdditivePath.displacement (start - 1)
            (rademacherIncrementPath branch) < 0 ∧
          AdditivePath.displacement start
            (rademacherIncrementPath branch) = 0} ∩
          (Combinatorics.Sequence.blockCoordinates start length) ⁻¹' event) =
      (iidSequenceLaw fairBoolMeasure)
        {branch : ℕ → Bool |
          AdditivePath.displacement (start - 1)
            (rademacherIncrementPath branch) < 0 ∧
          AdditivePath.displacement start
            (rademacherIncrementPath branch) = 0} *
        (iidSequenceLaw fairBoolMeasure)
          ((Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹' event) := by
  exact iidSequenceLaw_measure_prefix_inter_block_eq_mul
    fairBoolMeasure start length _
      (measurableSet_rademacher_positiveCrossing_prefix hstart) event hevent

/-- The corresponding factorization for a positive-to-zero prefix. -/
theorem measure_rademacher_negativeCrossing_inter_block_eq_mul
    (start length : ℕ) (hstart : 0 < start)
    (event : Set (Fin length → Bool)) (hevent : MeasurableSet event) :
    (iidSequenceLaw fairBoolMeasure)
        ({branch : ℕ → Bool |
          0 < AdditivePath.displacement (start - 1)
            (rademacherIncrementPath branch) ∧
          AdditivePath.displacement start
            (rademacherIncrementPath branch) = 0} ∩
          (Combinatorics.Sequence.blockCoordinates start length) ⁻¹' event) =
      (iidSequenceLaw fairBoolMeasure)
        {branch : ℕ → Bool |
          0 < AdditivePath.displacement (start - 1)
            (rademacherIncrementPath branch) ∧
          AdditivePath.displacement start
            (rademacherIncrementPath branch) = 0} *
        (iidSequenceLaw fairBoolMeasure)
          ((Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹' event) := by
  exact iidSequenceLaw_measure_prefix_inter_block_eq_mul
    fairBoolMeasure start length _
      (measurableSet_rademacher_negativeCrossing_prefix hstart) event hevent

end ProbabilityTheory.RandomWalk

end

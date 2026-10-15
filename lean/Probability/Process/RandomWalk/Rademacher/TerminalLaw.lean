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

- `ProbabilityTheory.RandomWalk.positiveSurvivesBlock`:
  the finite Boolean blocks whose $\pm1$ partial sums stay nonnegative.
- `ProbabilityTheory.RandomWalk.negativeSurvivesBlock`:
  the blocks whose reflected partial sums stay nonnegative.
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
- `ProbabilityTheory.RandomWalk.measure_rademacher_crossing_symmetry`:
  the two crossing-prefix events $\{S_{m-1}<0,S_m=0\}$ and
  $\{S_{m-1}>0,S_m=0\}$ have equal probability.
- `ProbabilityTheory.RandomWalk.measure_lastSignChangeIndex_eq_inter_block`:
  the joint mass of $\mu_n=m$ and a terminal block event is the sum
  of the two crossing-prefix masses multiplied by their respective
  one-sided surviving-block masses.

These are the prefix/suffix independence steps behind the final
simple-symmetric-walk argument on page 484 of Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned to
stay positive*, Ann. Probab. 4(3) (1976), 480--485.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

private theorem map_fairBoolMeasure_not :
    fairBoolMeasure.map Bool.not = fairBoolMeasure := by
  let p : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have hp : unitInterval.symm p = p := by
    apply Subtype.ext
    norm_num [unitInterval.coe_symm_eq, p]
  unfold fairBoolMeasure
  rw [map_bernoulliMeasure]
  simp only [Bool.not_false, Bool.not_true]
  unfold bernoulliMeasure
  change unitInterval.toNNReal p • Measure.dirac true +
      unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac false =
    unitInterval.toNNReal p • Measure.dirac false +
      unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac true
  rw [hp]
  ac_rfl

private theorem map_iidFairBool_flip :
    (iidSequenceLaw fairBoolMeasure).map (fun branch n => !branch n) =
      iidSequenceLaw fairBoolMeasure := by
  rw [iidSequenceLaw_map_coordinatewise fairBoolMeasure Bool.not
    (measurable_of_countable _), map_fairBoolMeasure_not]

private theorem measurable_flipBoolSequence :
    Measurable (fun branch : ℕ → Bool => fun k => !branch k) := by
  rw [measurable_pi_iff]
  intro k
  exact (measurable_of_countable Bool.not).comp (measurable_pi_apply k)

private theorem rademacherIncrementPath_flip (branch : ℕ → Bool) :
    rademacherIncrementPath (fun k => !branch k) =
      fun k => -rademacherIncrementPath branch k := by
  funext k
  cases h : branch k <;>
    simp [rademacherIncrementPath, rademacherOfBool, h]

/-- Finite Rademacher blocks with nonnegative partial sums. -/
def positiveSurvivesBlock (length : ℕ) : Set (Fin length → Bool) :=
  {block | FiniteSurvivesNonnegative (fun j => rademacherOfBool (block j))}

/-- Finite Rademacher blocks whose reflected partial sums are nonnegative. -/
def negativeSurvivesBlock (length : ℕ) : Set (Fin length → Bool) :=
  {block | FiniteSurvivesNonnegative (fun j => -rademacherOfBool (block j))}

private theorem measurable_blockRademacher (length : ℕ) :
    Measurable (fun block : Fin length → Bool =>
      (fun j : Fin length => rademacherOfBool (block j))) := by
  rw [measurable_pi_iff]
  intro j
  exact measurable_rademacherOfBool.comp (measurable_pi_apply j)

private theorem measurableSet_positiveSurvivesBlock (length : ℕ) :
    MeasurableSet (positiveSurvivesBlock length) :=
  (measurableSet_finiteSurvivesNonnegative length).preimage
    (measurable_blockRademacher length)

private theorem measurableSet_negativeSurvivesBlock (length : ℕ) :
    MeasurableSet (negativeSurvivesBlock length) := by
  exact (measurableSet_finiteSurvivesNonnegative length).preimage
    (measurable_pi_iff.mpr fun j =>
      (measurable_rademacherOfBool.comp (measurable_pi_apply j)).neg)

private theorem positiveSurvivesBlock_shift_iff
    (branch : ℕ → Bool) (start length : ℕ) :
    Combinatorics.Sequence.blockCoordinates start length branch ∈
      positiveSurvivesBlock length ↔
    SurvivesNonnegative length
      (fun k => rademacherIncrementPath branch (start + k)) := by
  exact finiteSurvivesNonnegative_blockCoordinates_iff
    length start (rademacherIncrementPath branch)

private theorem negativeSurvivesBlock_shift_iff
    (branch : ℕ → Bool) (start length : ℕ) :
    Combinatorics.Sequence.blockCoordinates start length branch ∈
      negativeSurvivesBlock length ↔
    SurvivesNonnegative length
      (fun k => -rademacherIncrementPath branch (start + k)) := by
  exact finiteSurvivesNonnegative_blockCoordinates_iff
    length start (fun k => -rademacherIncrementPath branch k)

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

/-- Reflection of every Rademacher step exchanges the two possible
directions of crossing into zero and preserves the IID fair-Boolean law. -/
theorem measure_rademacher_crossing_symmetry
    {start : ℕ} (hstart : 0 < start) :
    (iidSequenceLaw fairBoolMeasure)
      {branch : ℕ → Bool |
        AdditivePath.displacement (start - 1)
          (rademacherIncrementPath branch) < 0 ∧
        AdditivePath.displacement start
          (rademacherIncrementPath branch) = 0} =
    (iidSequenceLaw fairBoolMeasure)
      {branch : ℕ → Bool |
        0 < AdditivePath.displacement (start - 1)
          (rademacherIncrementPath branch) ∧
        AdditivePath.displacement start
          (rademacherIncrementPath branch) = 0} := by
  let flip : (ℕ → Bool) → (ℕ → Bool) := fun branch k => !branch k
  let negativeCrossing : Set (ℕ → Bool) :=
    {branch | AdditivePath.displacement (start - 1)
      (rademacherIncrementPath branch) < 0 ∧
      AdditivePath.displacement start (rademacherIncrementPath branch) = 0}
  let positiveCrossing : Set (ℕ → Bool) :=
    {branch | 0 < AdditivePath.displacement (start - 1)
      (rademacherIncrementPath branch) ∧
      AdditivePath.displacement start (rademacherIncrementPath branch) = 0}
  have hflip : flip ⁻¹' negativeCrossing = positiveCrossing := by
    ext branch
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, negativeCrossing,
      positiveCrossing, flip, rademacherIncrementPath_flip,
      AdditivePath.displacement_neg]
    constructor
    · rintro ⟨hneg, hzero⟩
      constructor <;> linarith
    · rintro ⟨hpos, hzero⟩
      constructor <;> linarith
  change (iidSequenceLaw fairBoolMeasure) negativeCrossing =
    (iidSequenceLaw fairBoolMeasure) positiveCrossing
  calc
    (iidSequenceLaw fairBoolMeasure) negativeCrossing =
        ((iidSequenceLaw fairBoolMeasure).map flip) negativeCrossing := by
      rw [show (iidSequenceLaw fairBoolMeasure).map flip =
        iidSequenceLaw fairBoolMeasure from map_iidFairBool_flip]
    _ = (iidSequenceLaw fairBoolMeasure) (flip ⁻¹' negativeCrossing) :=
      Measure.map_apply measurable_flipBoolSequence
        ((sequencePrefixFiltration (E := Bool)).le start _
          (measurableSet_rademacher_positiveCrossing_prefix hstart))
    _ = (iidSequenceLaw fairBoolMeasure) positiveCrossing := by rw [hflip]

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

/-- The finite last-sign-change event splits into two independent
crossing-prefix and one-sided-tail events. -/
theorem measure_lastSignChangeIndex_eq_inter_block
    (n start : ℕ) (hstart : 0 < start) (hbefore : start < n)
    (event : Set (Fin (n - start) → Bool)) (hevent : MeasurableSet event) :
    (iidSequenceLaw fairBoolMeasure)
        ({branch : ℕ → Bool |
          lastSignChangeIndex n (rademacherIncrementPath branch) = start} ∩
          (Combinatorics.Sequence.blockCoordinates start (n - start)) ⁻¹' event) =
      (iidSequenceLaw fairBoolMeasure)
        {branch : ℕ → Bool |
          AdditivePath.displacement (start - 1)
            (rademacherIncrementPath branch) < 0 ∧
          AdditivePath.displacement start
            (rademacherIncrementPath branch) = 0} *
        (iidSequenceLaw fairBoolMeasure)
          ((Combinatorics.Sequence.blockCoordinates 0 (n - start)) ⁻¹'
            (event ∩ positiveSurvivesBlock (n - start))) +
      (iidSequenceLaw fairBoolMeasure)
        {branch : ℕ → Bool |
          0 < AdditivePath.displacement (start - 1)
            (rademacherIncrementPath branch) ∧
          AdditivePath.displacement start
            (rademacherIncrementPath branch) = 0} *
        (iidSequenceLaw fairBoolMeasure)
          ((Combinatorics.Sequence.blockCoordinates 0 (n - start)) ⁻¹'
            (event ∩ negativeSurvivesBlock (n - start))) := by
  let block := Combinatorics.Sequence.blockCoordinates (E := Bool) start (n - start)
  let posPrefix : Set (ℕ → Bool) :=
    {branch | AdditivePath.displacement (start - 1)
      (rademacherIncrementPath branch) < 0 ∧
      AdditivePath.displacement start (rademacherIncrementPath branch) = 0}
  let negPrefix : Set (ℕ → Bool) :=
    {branch | 0 < AdditivePath.displacement (start - 1)
      (rademacherIncrementPath branch) ∧
      AdditivePath.displacement start (rademacherIncrementPath branch) = 0}
  let posEvent := posPrefix ∩
    block ⁻¹' (event ∩ positiveSurvivesBlock (n - start))
  let negEvent := negPrefix ∩
    block ⁻¹' (event ∩ negativeSurvivesBlock (n - start))
  have heq : {branch : ℕ → Bool |
      lastSignChangeIndex n (rademacherIncrementPath branch) = start} ∩
      block ⁻¹' event = posEvent ∪ negEvent := by
    ext branch
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_union, posEvent, negEvent, posPrefix, negPrefix]
    rw [rademacher_lastSignChangeIndex_eq_iff_crossing branch n start
      hstart hbefore]
    simp only [block]
    rw [positiveSurvivesBlock_shift_iff branch start (n - start),
      negativeSurvivesBlock_shift_iff branch start (n - start)]
    tauto
  have hposMeas : MeasurableSet posEvent := by
    apply MeasurableSet.inter
    · exact (sequencePrefixFiltration (E := Bool)).le start _
        (measurableSet_rademacher_positiveCrossing_prefix hstart)
    · exact (hevent.inter (measurableSet_positiveSurvivesBlock _)).preimage
        (measurable_blockCoordinates start (n - start))
  have hnegMeas : MeasurableSet negEvent := by
    apply MeasurableSet.inter
    · exact (sequencePrefixFiltration (E := Bool)).le start _
        (measurableSet_rademacher_negativeCrossing_prefix hstart)
    · exact (hevent.inter (measurableSet_negativeSurvivesBlock _)).preimage
        (measurable_blockCoordinates start (n - start))
  have hdisj : Disjoint posEvent negEvent := by
    apply Set.disjoint_left.mpr
    intro branch hpos hneg
    exact (lt_asymm hpos.1.1) hneg.1.1
  rw [heq, measure_union hdisj hnegMeas]
  rw [show posEvent = posPrefix ∩
      block ⁻¹' (event ∩ positiveSurvivesBlock (n - start)) from rfl,
    show negEvent = negPrefix ∩
      block ⁻¹' (event ∩ negativeSurvivesBlock (n - start)) from rfl]
  rw [measure_rademacher_positiveCrossing_inter_block_eq_mul start
      (n - start) hstart _
      (hevent.inter (measurableSet_positiveSurvivesBlock _)),
    measure_rademacher_negativeCrossing_inter_block_eq_mul start
      (n - start) hstart _
      (hevent.inter (measurableSet_negativeSurvivesBlock _))]

end ProbabilityTheory.RandomWalk

end

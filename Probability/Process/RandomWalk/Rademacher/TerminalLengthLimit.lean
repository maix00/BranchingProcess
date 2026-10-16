/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Rademacher.ConditionedPathLaw
public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.CLT

/-!
# Divergence of the terminal sign-stable length

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.tendsto_rademacher_returnProbability_zero`:
  for the simple symmetric walk $S_n$, $\mathbb P(S_n=0)\to0$.
- `ProbabilityTheory.RandomWalk.tendsto_booleanRademacher_returnProbability_zero`:
  the same estimate in the Boolean coding of the simple symmetric walk.
- `ProbabilityTheory.RandomWalk.tendsto_terminalSignStableLength_cell_zero`:
  for each fixed $r$, $\mathbb P(\nu_n=r)\to0$.
- `ProbabilityTheory.RandomWalk.tendsto_terminalSignStableLength_le_zero`:
  for each fixed $K$, $\mathbb P(\nu_n\le K)\to0$.

This is the return-probability input for the assertion $\nu_n\to\infty$
on page 484 of Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3)
(1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk

/-- The mass of a return to zero tends to zero for the simple symmetric
walk. This follows from its Gaussian central limit theorem and the absence
of atoms in the Gaussian law. -/
theorem tendsto_rademacher_returnProbability_zero :
    Tendsto (fun n : ℕ => (iidSequenceLaw rademacherMeasure)
      {increment : ℕ → ℝ | AdditivePath.displacement n increment = 0})
      atTop (nhds 0) := by
  have hcentered : (∫ x : ℝ, x ∂rademacherMeasure) = 0 := by
    rw [integral_rademacherMeasure]
    norm_num
  have hsecond : (∫ x : ℝ, x ^ 2 ∂rademacherMeasure) = 1 := by
    rw [integral_rademacherMeasure]
    norm_num
  have hclt := tendstoInDistribution_normalizedPartialSum
    rademacherMeasure hcentered hsecond
  have hzero : gaussianReal 0 1 ({0} : Set ℝ) = 0 := by
    exact (nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)).measure_singleton 0
  have hboundary : (gaussianReal 0 1).map id
      (frontier ({0} : Set ℝ)) = 0 := by
    rw [Measure.map_id]
    exact measure_mono_null (by
      simpa only [isClosed_singleton.closure_eq] using
        (frontier_subset_closure : frontier ({0} : Set ℝ) ⊆ closure {0})) hzero
  have hprob := hclt.tendsto_measure_map_of_null_frontier hboundary
  have hpre (n : ℕ) (hn : 0 < n) :
      (fun increment : ℕ → ℝ =>
        (Real.sqrt n)⁻¹ * AdditivePath.displacement n increment) ⁻¹'
          ({0} : Set ℝ) =
      {increment : ℕ → ℝ | AdditivePath.displacement n increment = 0} := by
    ext increment
    simp [Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hn)]
  have htail : ∀ᶠ n : ℕ in atTop,
      (iidSequenceLaw rademacherMeasure).map
        (fun increment =>
          (Real.sqrt n)⁻¹ * AdditivePath.displacement n increment)
          ({0} : Set ℝ) =
      (iidSequenceLaw rademacherMeasure)
        {increment : ℕ → ℝ | AdditivePath.displacement n increment = 0} := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [Measure.map_apply
      (show Measurable (fun increment : ℕ → ℝ =>
        (Real.sqrt n)⁻¹ * AdditivePath.displacement n increment) from
          measurable_const.mul (displacement_measurable n))
      (measurableSet_singleton 0), hpre n hn]
  rw [Measure.map_id, hzero] at hprob
  exact (tendsto_congr' htail).mp hprob

/-- Return probabilities in the Boolean realization of the simple
symmetric walk tend to zero. -/
theorem tendsto_booleanRademacher_returnProbability_zero :
    Tendsto (fun n : ℕ => (iidSequenceLaw fairBoolMeasure)
      {branch : ℕ → Bool |
        AdditivePath.displacement n (rademacherIncrementPath branch) = 0})
      atTop (nhds 0) := by
  have hmap (n : ℕ) :
      (iidSequenceLaw fairBoolMeasure)
          {branch : ℕ → Bool |
            AdditivePath.displacement n (rademacherIncrementPath branch) = 0} =
        (iidSequenceLaw rademacherMeasure)
          {increment : ℕ → ℝ | AdditivePath.displacement n increment = 0} := by
    rw [← map_iidSequenceLaw_rademacherIncrementPath,
      Measure.map_apply measurable_rademacherIncrementPath]
    · rfl
    · exact (measurableSet_singleton 0).preimage (displacement_measurable n)
  simpa only [hmap] using tendsto_rademacher_returnProbability_zero

/-- A fixed terminal length has vanishing mass: on `νₙ = r`, the
starting position `n - r` of the last sign-stable segment is a return
to zero. -/
theorem tendsto_terminalSignStableLength_cell_zero (length : ℕ) :
    Tendsto (fun n : ℕ => (iidSequenceLaw fairBoolMeasure)
      {branch : ℕ → Bool |
        terminalSignStableLength n (rademacherIncrementPath branch) = length})
      atTop (nhds 0) := by
  have hupper : Tendsto (fun n : ℕ => (iidSequenceLaw fairBoolMeasure)
      {branch : ℕ → Bool |
        AdditivePath.displacement (n - length)
          (rademacherIncrementPath branch) = 0}) atTop (nhds 0) :=
    tendsto_booleanRademacher_returnProbability_zero.comp
      (tendsto_sub_atTop_nat length)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (nhds 0))
    hupper
  · exact Eventually.of_forall fun n => bot_le
  · filter_upwards [eventually_ge_atTop length] with n hn
    apply measure_mono
    intro branch hbranch
    have hμ : lastSignChangeIndex n (rademacherIncrementPath branch) =
        n - length := by
      have hindex := lastSignChangeIndex_le n (rademacherIncrementPath branch)
      change n - lastSignChangeIndex n (rademacherIncrementPath branch) =
        length at hbranch
      omega
    simpa only [Set.mem_ofPred_eq, ← hμ] using
      rademacher_displacement_lastSignChange_eq_zero branch n

/-- Bolthausen's terminal length escapes every finite set in probability. -/
theorem tendsto_terminalSignStableLength_le_zero (bound : ℕ) :
    Tendsto (fun n : ℕ => (iidSequenceLaw fairBoolMeasure)
      {branch : ℕ → Bool |
        terminalSignStableLength n (rademacherIncrementPath branch) ≤ bound})
      atTop (nhds 0) := by
  let cell (n length : ℕ) : Set (ℕ → Bool) :=
    {branch | terminalSignStableLength n
      (rademacherIncrementPath branch) = length}
  have hunion (n : ℕ) :
      {branch : ℕ → Bool |
        terminalSignStableLength n (rademacherIncrementPath branch) ≤ bound} =
        ⋃ length ∈ Finset.range (bound + 1), cell n length := by
    ext branch
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, cell]
    constructor
    · intro h
      exact ⟨_, by omega, rfl⟩
    · rintro ⟨length, hlength, heq⟩
      omega
  have hsum : Tendsto (fun n : ℕ =>
      ∑ length ∈ Finset.range (bound + 1),
        (iidSequenceLaw fairBoolMeasure) (cell n length)) atTop (nhds 0) := by
    simpa only [cell, Finset.sum_const_zero] using
      (tendsto_finsetSum (Finset.range (bound + 1))
        (fun length _ => tendsto_terminalSignStableLength_cell_zero length))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (nhds 0))
    hsum
  · exact Eventually.of_forall fun n => bot_le
  · exact Eventually.of_forall fun n => by
      rw [hunion]
      exact measure_biUnion_finset_le _ _

end ProbabilityTheory.RandomWalk

end

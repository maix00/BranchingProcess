/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PartitionLower.WidthRate
import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Partition.LowerEnergy

/-!
# The exact energy lower rate for M₂ corridors.
-/

open Skorokhod.PathClass.StepCorridor

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open Skorokhod.PathClass.StepCorridor
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

/-- Every positive error admits an eventual finite-partition lower bound for
the full `M₂` energy. The statement keeps the positivity needed for real
logarithms together with the quantitative bound, so it can be combined
directly with an upper limsup estimate. -/
theorem eventually_stableSmallDeviationRate_mul_log_normalizedStepCorridor_ge_energy
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (c : ContinuousAdmissibleStepCorridor) {error : ℝ} (herror : 0 < error) :
    ∀ᶠ n : ℕ in atTop,
      0 < iidSequenceLaw ν {increment : ℕ → ℝ |
        RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
          Skorokhod.PathClass.StepCorridor.corridorSet
            c.upper c.lower} ∧
      C * 2 ^ α * (c.energy α).toReal - error ≤
        stableSmallDeviationRate α ν scale n * Real.log
          (iidSequenceLaw ν {increment : ℕ → ℝ |
            RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
              Skorokhod.PathClass.StepCorridor.corridorSet
                c.upper c.lower}).toReal := by
  classical
  obtain ⟨hstart, hsep⟩ :=
    hasContinuousAdmissiblePath_implies_startAndTraceSeparated
      c.hasContinuousAdmissiblePath
  let targetRate : ℝ := C * 2 ^ α * (c.energy α).toReal
  let corridorProbability (n : ℕ) : ENNReal :=
    iidSequenceLaw ν {increment : ℕ → ℝ |
      RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.PathClass.StepCorridor.corridorSet
          c.upper c.lower}
  let corridorRate (n : ℕ) : ℝ :=
    stableSmallDeviationRate α ν scale n * Real.log (corridorProbability n).toReal
  let approximation (m : ℕ) : ℝ :=
    ∑ i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1),
      C * commonPartitionCellLength c.upper c.lower i /
        ((commonPartitionApproxWidth c.upper c.lower m i / 2) ^ α)
  have happroximation := c.tendsto_commonPartitionApproxRate C α hsep hα
  have happroximationNear : ∀ᶠ m : ℕ in atTop,
      targetRate - error / 2 < approximation m := by
    have hlt : targetRate - error / 2 < targetRate := by linarith
    have hmem := happroximation.eventually (isOpen_Ioi.mem_nhds hlt)
    simpa [approximation, targetRate, Set.mem_Ioi] using hmem
  obtain ⟨m, hm⟩ := happroximationNear.exists
  let targetWidth : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1) → ℝ :=
    fun i => commonPartitionApproxWidth c.upper c.lower m i
  have htarget : ∀ i, 0 < targetWidth i := by
    intro i
    exact commonPartitionApproxWidth_pos c.upper c.lower hsep m i
  have hwidth : ∀ i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1),
      c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) = ⊥ ∨
      c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) = ⊤ ∨
      targetWidth i <
        (c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)).toReal -
          (c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)).toReal := by
    intro i
    exact commonPartitionApproxWidth_lt_traceWidth c.upper c.lower hsep m i
  have htargetRate :=
    eventually_iidSequenceLaw_normalizedStepCorridor_ge_targetRate
      hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase c.upper c.lower
      hstart hsep targetWidth htarget hwidth (by linarith : 0 < error / 2)
  have happroximationLower : targetRate - error / 2 <
      ∑ i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1),
        C * commonPartitionCellLength c.upper c.lower i /
          ((targetWidth i / 2) ^ α) := by
    simpa [approximation, targetWidth, targetRate] using hm
  filter_upwards [htargetRate] with n hn
  rcases hn with ⟨hpositive, hrate⟩
  have hrate' :
      (∑ i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1),
        C * commonPartitionCellLength c.upper c.lower i /
          ((targetWidth i / 2) ^ α)) - error / 2 ≤ corridorRate n := by
    simpa [corridorRate, corridorProbability] using hrate
  refine ⟨hpositive, ?_⟩
  change targetRate - error ≤ corridorRate n
  linarith [happroximationLower, hrate']

/-- The exact lower logarithmic rate for an `M₂` step corridor follows by
approximating each extended-real cell width from below and applying the
finite-target estimate. This is the discrete finite-partition lower half of
the stable Mogulskii theorem. -/
theorem liminf_stableSmallDeviationRate_mul_log_normalizedStepCorridor_ge_energy
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (c : ContinuousAdmissibleStepCorridor) :
    C * 2 ^ α * (c.energy α).toReal ≤ atTop.liminf (fun n =>
      stableSmallDeviationRate α ν scale n * Real.log
        (iidSequenceLaw ν {increment : ℕ → ℝ |
          RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
            Skorokhod.PathClass.StepCorridor.corridorSet
              c.upper c.lower}).toReal) := by
  classical
  obtain ⟨hstart, hsep⟩ :=
    hasContinuousAdmissiblePath_implies_startAndTraceSeparated
      c.hasContinuousAdmissiblePath
  let targetRate : ℝ := C * 2 ^ α * (c.energy α).toReal
  let corridorProbability (n : ℕ) : ENNReal :=
    iidSequenceLaw ν {increment : ℕ → ℝ |
      RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.PathClass.StepCorridor.corridorSet c.upper c.lower}
  let corridorRate (n : ℕ) : ℝ :=
    stableSmallDeviationRate α ν scale n * Real.log (corridorProbability n).toReal
  have heventualLower (error : ℝ) (herror : 0 < error) :
      ∀ᶠ n : ℕ in atTop, targetRate - error ≤ corridorRate n := by
    let approximation (m : ℕ) : ℝ :=
      ∑ i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1),
        C * commonPartitionCellLength c.upper c.lower i /
          ((commonPartitionApproxWidth c.upper c.lower m i / 2) ^ α)
    have happroximation := c.tendsto_commonPartitionApproxRate C α hsep hα
    have happroximationNear : ∀ᶠ m : ℕ in atTop,
        targetRate - error / 2 < approximation m := by
      have hlt : targetRate - error / 2 < targetRate := by linarith
      have hmem := happroximation.eventually (isOpen_Ioi.mem_nhds hlt)
      simpa [approximation, targetRate, Set.mem_Ioi] using hmem
    obtain ⟨m, hm⟩ := happroximationNear.exists
    let targetWidth : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1) → ℝ :=
      fun i => commonPartitionApproxWidth c.upper c.lower m i
    have htarget : ∀ i, 0 < targetWidth i := by
      intro i
      exact commonPartitionApproxWidth_pos c.upper c.lower hsep m i
    have hwidth : ∀ i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1),
        c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) = ⊥ ∨
        c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) = ⊤ ∨
        targetWidth i <
          (c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)).toReal -
            (c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)).toReal := by
      intro i
      exact commonPartitionApproxWidth_lt_traceWidth c.upper c.lower hsep m i
    have htargetRate :=
      eventually_iidSequenceLaw_normalizedStepCorridor_ge_targetRate
        hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase c.upper c.lower
        hstart hsep targetWidth htarget hwidth (by linarith : 0 < error / 2)
    filter_upwards [htargetRate] with n hn
    rcases hn with ⟨_, hrate⟩
    have happroximationLower : targetRate - error / 2 <
        ∑ i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1),
          C * commonPartitionCellLength c.upper c.lower i /
            ((targetWidth i / 2) ^ α) := by
      simpa [approximation, targetWidth, targetRate] using hm
    have hrate' :
        (∑ i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1),
          C * commonPartitionCellLength c.upper c.lower i /
            ((targetWidth i / 2) ^ α)) - error / 2 ≤ corridorRate n := by
      simpa [corridorRate, corridorProbability] using hrate
    exact le_trans (by linarith [happroximationLower]) hrate'
  have hrateNonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ stableSmallDeviationRate α ν scale n := by
    have hscaleTop := hscale.scale_tendsto_atTop
    have hslowPos : ∀ᶠ n : ℕ in atTop,
        0 < stableSlowVariation α ν (scale n) :=
      hscaleTop.eventually hslow.eventually_pos
    filter_upwards [eventually_gt_atTop (0 : ℕ), hscale.eventually_scale_pos,
      hslowPos] with n hn hs hL
    rw [stableSmallDeviationRate]
    have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hprobabilityLeOne (n : ℕ) : corridorProbability n ≤ 1 := by
    calc
      corridorProbability n ≤ iidSequenceLaw ν Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hrateLeZero : ∀ᶠ n : ℕ in atTop, corridorRate n ≤ 0 := by
    filter_upwards [hrateNonneg] with n hrate
    have hprobabilityTop : corridorProbability n ≠ ⊤ :=
      ne_of_lt ((hprobabilityLeOne n).trans_lt ENNReal.one_lt_top)
    have hprobabilityRealLe : (corridorProbability n).toReal ≤ 1 :=
      (ENNReal.toReal_le_toReal hprobabilityTop ENNReal.one_ne_top).2
        (hprobabilityLeOne n)
    have hlogNonpos : Real.log (corridorProbability n).toReal ≤ 0 :=
      Real.log_nonpos ENNReal.toReal_nonneg hprobabilityRealLe
    exact mul_nonpos_of_nonneg_of_nonpos hrate hlogNonpos
  have hrateUpperBounded : Filter.IsCoboundedUnder (· ≥ ·) atTop corridorRate :=
    Filter.isCoboundedUnder_ge_of_eventually_le atTop hrateLeZero
  have hrateLowerBounded : Filter.IsBoundedUnder (· ≥ ·) atTop corridorRate :=
    Filter.isBoundedUnder_of_eventually_ge (heventualLower 1 (by norm_num))
  apply (Filter.le_liminf_iff hrateUpperBounded hrateLowerBounded).2
  intro y hy
  have herror : 0 < (targetRate - y) / 2 := by linarith
  have hnear := heventualLower ((targetRate - y) / 2) herror
  filter_upwards [hnear] with n hn
  have hyRate : y < targetRate - (targetRate - y) / 2 := by linarith
  exact hyRate.trans_le hn


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.SmallDeviation.Mogulskii.PathClass.Partition.LowerApproximation
import Probability.Process.SmallDeviation.Mogulskii.PathClass.Partition.LowerEnergy
import Probability.Process.Stable.SmallDeviation.Mogulskii.PathClass.Partition.LowerRate

/-! # Stable-process lower rate for approximating partition widths -/

open Filter MeasureTheory
open scoped NNReal Topology

@[expose] public section

namespace ProbabilityTheory

open ProbabilityTheory.Process.SmallDeviation.Mogulskii

/-- The stable-process lower bound holds with any prescribed cell widths that
lie strictly below the corresponding boundary widths. This is the sharpness
interface: finite boundary widths are approached from below, while an
infinite-width cell permits targets tending to infinity. -/
theorem HasStableProcessEscapeRate.eventually_scaledCorridorLog_ge_targetPartitionRate
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower)
    (target : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (htarget : ∀ i, 0 < target i)
    (hwidth : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊥ ∨
      upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊤ ∨
      target i <
        (upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
          (lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal)
    (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ scale : ℝ in atTop,
      0 < P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower) ∧
      (∑ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        C * commonPartitionCellLength upper lower i /
          ((target i / 2) ^ α)) - ε ≤
        scale⁻¹ ^ α * Real.log
          ((P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower)).toReal) := by
  obtain ⟨center, radius, innerLower, innerUpper, hcenter0, hradius0,
      hradiusNonneg, hradiusStep, hcores, hgeometry, htargetWidth⟩ :=
    exists_commonPartitionInnerGeometry_withWidth upper lower hstart hsep
      target htarget hwidth
  let targetRate : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ :=
    fun i => C * commonPartitionCellLength upper lower i / ((target i / 2) ^ α)
  let innerRate : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ :=
    fun i => C * commonPartitionCellLength upper lower i /
      (((innerUpper i - innerLower i) / 2) ^ α)
  have hrateMono : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      targetRate i ≤ innerRate i := by
    intro i
    have htargetInner : target i / 2 < (innerUpper i - innerLower i) / 2 := by
      linarith [htargetWidth i]
    have htargetPos : 0 < target i / 2 := by
      exact div_pos (htarget i) (by norm_num)
    have hinnerPos : 0 < (innerUpper i - innerLower i) / 2 := by
      linarith
    have hpow : (target i / 2) ^ α ≤ ((innerUpper i - innerLower i) / 2) ^ α :=
      Real.rpow_le_rpow htargetPos.le htargetInner.le hα.le
    have htargetPowPos : 0 < (target i / 2) ^ α :=
      Real.rpow_pos_of_pos htargetPos α
    have hinnerPowPos : 0 < ((innerUpper i - innerLower i) / 2) ^ α :=
      Real.rpow_pos_of_pos hinnerPos α
    have hnum : C * commonPartitionCellLength upper lower i < 0 :=
      mul_neg_of_neg_of_pos hEscape.negative
        (commonPartitionCellLength_pos upper lower i)
    apply (div_le_div_iff₀ htargetPowPos hinnerPowPos).2
    exact mul_le_mul_of_nonpos_left hpow hnum.le
  have hsumMono : (∑ i, targetRate i) ≤ ∑ i, innerRate i :=
    Finset.sum_le_sum (fun i hi => hrateMono i)
  have hfixed :=
    HasStableProcessEscapeRate.eventually_scaledCorridorLog_ge_fixedInnerRate
      hEscape hX hcdf upper lower center radius innerLower innerUpper
      hcenter0 hradius0 hcores hradiusNonneg hradiusStep hgeometry hα
      (ε := ε / 2) (by linarith)
  have hmono : ∀ scale : ℝ,
      0 < P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower) ∧
      (∑ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        C * commonPartitionCellLength upper lower i /
          (((innerUpper i - innerLower i) / 2) ^ α)) - ε / 2 ≤
          scale⁻¹ ^ α * Real.log
            ((P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower)).toReal) →
      0 < P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower) ∧
        (∑ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
          C * commonPartitionCellLength upper lower i /
            ((target i / 2) ^ α)) - ε ≤
          scale⁻¹ ^ α * Real.log
            ((P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower)).toReal) := by
    intro scale ⟨hpositive, hscale⟩
    exact ⟨hpositive, by linarith [hsumMono]⟩
  exact Filter.Eventually.mono hfixed hmono

end ProbabilityTheory

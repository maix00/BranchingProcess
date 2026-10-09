/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.Stable.SmallDeviation.PathClass.StepCorridor.Partition.LowerApproximationRate
import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Partition.LowerEnergy

/-! # Stable-process lower rate and exact corridor energy -/

open Filter MeasureTheory
open scoped NNReal Topology

open Skorokhod.PathClass.StepCorridor

@[expose] public section

namespace ProbabilityTheory

open Skorokhod.PathClass.StepCorridor

/-- Passing the finite inner widths to their limit gives the stable-process
lower bound with the exact corridor energy. This is the `M₂` lower-rate
bridge; it does not assume a finite-valued boundary on any partition cell. -/
theorem HasStableProcessEscapeRate.eventually_scaledCorridorLog_ge_energyRate
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (c : ContinuousAdmissibleStepCorridor)
    (hstart : StartAdmissible c.upper c.lower)
    (hsep : TraceSeparated c.upper c.lower)
    (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ scale : ℝ in atTop,
      0 < P ((Skorokhod.scalePath scale) ⁻¹' corridorSet c.upper c.lower) ∧
      C * 2 ^ α * (c.energy α).toReal - ε ≤
        scale⁻¹ ^ α * Real.log
          ((P ((Skorokhod.scalePath scale) ⁻¹' corridorSet c.upper c.lower)).toReal) := by
  let rate := fun n : ℕ =>
    ∑ i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1),
      C * commonPartitionCellLength c.upper c.lower i /
        ((commonPartitionApproxWidth c.upper c.lower n i / 2) ^ α)
  let limit := C * 2 ^ α * (c.energy α).toReal
  have hrate := c.tendsto_commonPartitionApproxRate C α hsep hα
  have hnear : ∀ᶠ n : ℕ in atTop, dist (rate n) limit < ε / 2 := by
    exact hrate.eventually (Metric.ball_mem_nhds limit (by linarith))
  obtain ⟨n, hn⟩ := hnear.exists
  have hrateLower : limit - ε / 2 < rate n := by
    have habs : |rate n - limit| < ε / 2 := by
      simpa [Real.dist_eq] using hn
    rcases abs_lt.mp habs with ⟨hlo, hhi⟩
    linarith
  let target : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1) → ℝ :=
    fun i => commonPartitionApproxWidth c.upper c.lower n i
  have htarget : ∀ i, 0 < target i := by
    intro i
    exact commonPartitionApproxWidth_pos c.upper c.lower hsep n i
  have hwidth : ∀ i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1),
      c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) = ⊥ ∨
      c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) = ⊤ ∨
      target i <
        (c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)).toReal -
          (c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)).toReal := by
    intro i
    exact commonPartitionApproxWidth_lt_traceWidth c.upper c.lower hsep n i
  have htargetLower :=
    HasStableProcessEscapeRate.eventually_scaledCorridorLog_ge_targetPartitionRate
    hEscape
    hX hcdf c.upper c.lower hstart hsep target htarget hwidth hα
      (ε := ε / 2) (by linarith)
  have hrateLower' : limit - ε / 2 <
      ∑ i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1),
        C * commonPartitionCellLength c.upper c.lower i /
          ((target i / 2) ^ α) := by
    simpa [rate, target, limit] using hrateLower
  filter_upwards [htargetLower] with scale hresult
  have hscale' :
      (∑ i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1),
        C * commonPartitionCellLength c.upper c.lower i /
          ((target i / 2) ^ α)) - ε / 2 ≤
        scale⁻¹ ^ α * Real.log
          ((P ((Skorokhod.scalePath scale) ⁻¹' corridorSet c.upper c.lower)).toReal) := by
    simpa [target] using hresult.2
  exact ⟨hresult.1, by linarith⟩


end ProbabilityTheory

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Partition.UpperEnergy
public import Probability.Process.Stable.SmallDeviation.PathClass.StepCorridor.Partition.LowerEnergyRate
public import Probability.Process.Stable.SmallDeviation.PathClass.StepCorridor.Partition.Scaled

/-! # Stable-process upper rate and exact corridor energy -/

open Filter MeasureTheory
open scoped NNReal Topology

open Skorokhod.PathClass.StepCorridor

@[expose] public section

namespace ProbabilityTheory

open Skorokhod.PathClass.StepCorridor

/-- The stable-process `M₂` upper rate follows from the range-tube product
bound on finite-width cells. Infinite-width cells impose no range restriction
and have zero `Hα` cost. Together with the lower estimate this gives the exact
two-sided `M₂` rate without a boundary-null assumption. -/
theorem HasStableProcessEscapeRate.eventually_scaledCorridorLog_le_energyRate
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (c : ContinuousAdmissibleStepCorridor)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ scale : ℝ in atTop,
      scale⁻¹ ^ α * Real.log
        ((P ((Skorokhod.scalePath scale) ⁻¹' corridorSet c.upper c.lower)).toReal) ≤
        C * 2 ^ α * (c.energy α).toReal + ε := by
  classical
  have hsep := hasContinuousAdmissiblePath_implies_traceSeparated
    c.hasContinuousAdmissiblePath
  let s := Finset.univ.filter (fun i : Fin
    ((StepBoundary.commonKnots c.upper c.lower).card - 1) =>
      c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) ≠ ⊤ ∧
      c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) ≠ ⊥)
  let lo : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1) → ℝ := fun i =>
    (c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)).toReal
  let hi : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1) → ℝ := fun i =>
    (c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)).toReal
  have hfiniteEnergy := c.energy_toReal_eq_finiteCellRate α hsep
  have hwidth (i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1))
      (hiMem : i ∈ s) : lo i < hi i := by
    have htrace := rightTrace_lt_of_traceSeparated c.upper c.lower hsep
      (StepBoundary.commonPartitionGrid c.upper c.lower i.val)
    change
      c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) <
        c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) at htrace
    have hmem := Finset.mem_filter.mp hiMem
    have hLtop :
        c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) ≠ ⊤ := by
      intro h
      rw [h] at htrace
      exact (not_lt_of_ge le_top) htrace
    have hUbot :
        c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) ≠ ⊥ := by
      intro h
      rw [h] at htrace
      exact (not_lt_of_ge bot_le) htrace
    have hLcoe := EReal.coe_toReal hLtop hmem.2.2
    have hUcoe := EReal.coe_toReal hmem.2.1 hUbot
    rw [← hLcoe, ← hUcoe] at htrace
    exact EReal.coe_lt_coe_iff.mp htrace
  have hrateTendsto := tendsto_relativePartitionRate_vanishingEnlargement
    (α := α) (C := C) s (fun i =>
      commonPartitionCellLength c.upper c.lower i / (hi i - lo i) ^ α)
  have hrateLimit :
      C * 2 ^ α * ∑ i ∈ s,
          commonPartitionCellLength c.upper c.lower i / (hi i - lo i) ^ α =
        C * 2 ^ α * (c.energy α).toReal := by
    rw [← hfiniteEnergy]
  have hnear : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      C * (2 / (1 + δ)) ^ α *
        ∑ i ∈ s, commonPartitionCellLength c.upper c.lower i /
          (hi i - lo i) ^ α < C * 2 ^ α * (c.energy α).toReal + ε / 2 := by
    have hlimit := hrateTendsto
    rw [hrateLimit] at hlimit
    exact hlimit.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨δ, hδrate, hδpos⟩ := (hnear.and self_mem_nhdsWithin).exists
  have hlower := HasStableProcessEscapeRate.eventually_scaledCorridorLog_ge_energyRate
    hEscape hX hcdf c
      (hasContinuousAdmissiblePath_implies_startAdmissible
        c.hasContinuousAdmissiblePath)
      hsep (hEscape.isStableClockProcessLaw.strictlyStable.1)
      (ε := ε / 2) (by linarith)
  have hpositive : ∀ᶠ scale : ℝ in atTop,
      0 < (P ((Skorokhod.scalePath scale) ⁻¹' corridorSet c.upper c.lower)).toReal := by
    filter_upwards [hlower] with scale hscale
    exact ENNReal.toReal_pos hscale.1.ne' (measure_ne_top P _)
  have hupper := HasStableProcessEscapeRate.eventually_scalePath_corridor_logRate_le
    hEscape hX c.upper c.lower s lo hi
    (by
      intro i hiMem
      have hmem := Finset.mem_filter.mp hiMem
      exact EReal.coe_toReal
        (by
          intro h
          have htrace := rightTrace_lt_of_traceSeparated c.upper c.lower hsep
            (StepBoundary.commonPartitionGrid c.upper c.lower i.val)
          rw [h] at htrace
          exact (not_lt_of_ge le_top) htrace)
        hmem.2.2 |>.symm)
    (by
      intro i hiMem
      have hmem := Finset.mem_filter.mp hiMem
      exact EReal.coe_toReal hmem.2.1
        (by
          intro h
          have htrace := rightTrace_lt_of_traceSeparated c.upper c.lower hsep
            (StepBoundary.commonPartitionGrid c.upper c.lower i.val)
          rw [h] at htrace
          exact (not_lt_of_ge bot_le) htrace) |>.symm)
    hwidth (ε := δ) (η := ε / 2) hδpos (by linarith) hpositive
  filter_upwards [hupper] with scale hscale
  linarith

/-- Exact stable-process small-width asymptotics for every admissible `M₂`
step corridor. The positivity clause records that the real logarithm is taken
on a genuinely positive corridor probability eventually. -/
theorem HasStableProcessEscapeRate.tendsto_scaledCorridorLog_eq_energyRate
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (c : ContinuousAdmissibleStepCorridor) :
    (∀ᶠ scale : ℝ in atTop,
      0 < (P ((Skorokhod.scalePath scale) ⁻¹' corridorSet c.upper c.lower)).toReal) ∧
    Tendsto
      (fun scale : ℝ => scale⁻¹ ^ α * Real.log
        ((P ((Skorokhod.scalePath scale) ⁻¹' corridorSet c.upper c.lower)).toReal))
      atTop (𝓝 (C * 2 ^ α * (c.energy α).toReal)) := by
  let target : ℝ := C * 2 ^ α * (c.energy α).toReal
  have hsep := hasContinuousAdmissiblePath_implies_traceSeparated
    c.hasContinuousAdmissiblePath
  have hstart := hasContinuousAdmissiblePath_implies_startAdmissible
    c.hasContinuousAdmissiblePath
  have hα := hEscape.isStableClockProcessLaw.strictlyStable.1
  have hlower := HasStableProcessEscapeRate.eventually_scaledCorridorLog_ge_energyRate
    hEscape hX hcdf c hstart hsep hα (ε := 1) (by norm_num)
  have hpositive : ∀ᶠ scale : ℝ in atTop,
      0 < (P ((Skorokhod.scalePath scale) ⁻¹' corridorSet c.upper c.lower)).toReal := by
    filter_upwards [hlower] with scale hscale
    exact ENNReal.toReal_pos hscale.1.ne' (measure_ne_top P _)
  have hlimit : Tendsto
      (fun scale : ℝ => scale⁻¹ ^ α * Real.log
        ((P ((Skorokhod.scalePath scale) ⁻¹' corridorSet c.upper c.lower)).toReal))
      atTop (𝓝 target) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro y hy
      have hε : 0 < (target - y) / 2 := by linarith
      have hbound := HasStableProcessEscapeRate.eventually_scaledCorridorLog_ge_energyRate
        hEscape hX hcdf c hstart hsep hα (ε := (target - y) / 2) hε
      filter_upwards [hbound] with scale hscale
      have hstrict : y < target - (target - y) / 2 := by linarith
      exact lt_of_lt_of_le hstrict (by simpa [target] using hscale.2)
    · intro y hy
      have hε : 0 < (y - target) / 2 := by linarith
      have hbound := HasStableProcessEscapeRate.eventually_scaledCorridorLog_le_energyRate
        hEscape hX hcdf c (ε := (y - target) / 2) hε
      filter_upwards [hbound] with scale hscale
      have hstrict : target + (y - target) / 2 < y := by linarith
      exact lt_of_le_of_lt (by simpa [target] using hscale) hstrict
  exact ⟨hpositive, hlimit⟩

end ProbabilityTheory

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.SmallDeviation.Mogulskii.PathClass.Partition.LowerEnergy
import Probability.Process.SmallDeviation.Mogulskii.PathClass.Partition.Scaled

/-!
# Stable-process corridor upper rate and exact `M₂` asymptotics

The upper estimate uses only the finite-width cells of the common partition;
infinite-width cells carry no restriction and have zero energy. Combined with
the lower construction, this proves the exact stable-process rate for every
admissible `M₂` step corridor.
-/

open Filter MeasureTheory
open scoped NNReal Topology

@[expose] public section

namespace ProbabilityTheory.Process.SmallDeviation.Mogulskii

/-- The finite-width cells are exactly the cells that contribute to the
`Hα` energy. Their common-partition rate sum is the real-valued energy. -/
theorem M2Corridor.energy_toReal_eq_finiteCellRate
    (α : ℝ) (c : M2Corridor) (hsep : TraceSeparated c.upper c.lower) :
    let s := Finset.univ.filter (fun i : Fin
      ((StepBoundary.commonKnots c.upper c.lower).card - 1) =>
        c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) ≠ ⊤ ∧
        c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) ≠ ⊥)
    let lo : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1) → ℝ := fun i =>
      (c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)).toReal
    let hi : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1) → ℝ := fun i =>
      (c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)).toReal
    (c.energy α).toReal = ∑ i ∈ s,
      commonPartitionCellLength c.upper c.lower i / (hi i - lo i) ^ α := by
  classical
  dsimp only
  let s := Finset.univ.filter (fun i : Fin
    ((StepBoundary.commonKnots c.upper c.lower).card - 1) =>
      c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) ≠ ⊤ ∧
      c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) ≠ ⊥)
  let lo : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1) → ℝ := fun i =>
    (c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)).toReal
  let hi : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1) → ℝ := fun i =>
    (c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)).toReal
  let U (i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1)) :=
    c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)
  let L (i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1)) :=
    c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)
  have htraces (i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1))
      (hiMem : i ∈ s) : L i = (lo i : EReal) ∧ U i = (hi i : EReal) := by
    have hmem := Finset.mem_filter.mp hiMem
    have hsepI := rightTrace_lt_of_traceSeparated c.upper c.lower hsep
      (StepBoundary.commonPartitionGrid c.upper c.lower i.val)
    change L i < U i at hsepI
    have hLtop : L i ≠ ⊤ := by
      intro h
      rw [h] at hsepI
      exact (not_lt_of_ge le_top) hsepI
    have hUbot : U i ≠ ⊥ := by
      intro h
      rw [h] at hsepI
      exact (not_lt_of_ge bot_le) hsepI
    have hLcoe : (L i).toReal = L i := EReal.coe_toReal hLtop hmem.2.2
    have hUcoe : (U i).toReal = U i := EReal.coe_toReal hmem.2.1 hUbot
    exact ⟨hLcoe.symm, hUcoe.symm⟩
  have hwidth (i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1))
      (hiMem : i ∈ s) : lo i < hi i := by
    have htrace := rightTrace_lt_of_traceSeparated c.upper c.lower hsep
      (StepBoundary.commonPartitionGrid c.upper c.lower i.val)
    change L i < U i at htrace
    rcases htraces i hiMem with ⟨hL, hU⟩
    rw [hL, hU] at htrace
    exact EReal.coe_lt_coe_iff.mp htrace
  have hcost (i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1))
      (hiMem : i ∈ s) :
      (widthCost α (U i) (L i)).toReal = (hi i - lo i) ^ (-α) := by
    rcases htraces i hiMem with ⟨hL, hU⟩
    rw [hL, hU]
    rw [widthCost_coe_sub α (hi i) (lo i) (sub_pos.mpr (hwidth i hiMem))]
    rw [ENNReal.toReal_ofReal]
    exact Real.rpow_nonneg (sub_nonneg.mpr (le_of_lt (hwidth i hiMem))) _
  have hterm (i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1))
      (hiMem : i ∈ s) :
      (widthCost α (U i) (L i)).toReal * commonPartitionCellLength c.upper c.lower i =
        commonPartitionCellLength c.upper c.lower i / (hi i - lo i) ^ α := by
    rw [hcost i hiMem, Real.rpow_neg (le_of_lt (sub_pos.mpr (hwidth i hiMem))) α]
    simp [div_eq_mul_inv, mul_comm]
  have hzero (i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1))
      (hi : i ∉ s) :
      (widthCost α (U i) (L i)).toReal * commonPartitionCellLength c.upper c.lower i = 0 := by
    have hpred : ¬ (U i ≠ ⊤ ∧ L i ≠ ⊥) := by
      intro hcond
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcond⟩)
    by_cases hU : U i = ⊤
    · simp [hU]
    · have hL : L i = ⊥ := by
        by_contra hL
        exact hpred ⟨hU, hL⟩
      simp [hL]
  rw [c.energy_toReal_eq_commonPartitionCellFinSum α]
  calc
    _ = ∑ i ∈ s,
        (widthCost α (U i) (L i)).toReal *
          commonPartitionCellLength c.upper c.lower i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i hiUniv hiNot
      exact hzero i hiNot
    _ = ∑ i ∈ s,
        commonPartitionCellLength c.upper c.lower i / (hi i - lo i) ^ α := by
      apply Finset.sum_congr rfl
      intro i hiMem
      exact hterm i hiMem

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
    (c : M2Corridor)
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
    (c : M2Corridor) :
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

end ProbabilityTheory.Process.SmallDeviation.Mogulskii

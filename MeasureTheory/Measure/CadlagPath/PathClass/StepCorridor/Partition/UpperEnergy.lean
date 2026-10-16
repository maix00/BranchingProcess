/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Partition.LowerEnergy
public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Partition.LowerCores

/-!
# Stable-process corridor upper rate and exact `M₂` asymptotics

The upper estimate uses only the finite-width cells of the common partition;
infinite-width cells carry no restriction and have zero energy. Combined with
the lower construction, this proves the exact stable-process rate for every
admissible `M₂` step corridor.
-/

open Filter MeasureTheory
open scoped NNReal Topology

open Skorokhod.PathClass.StepCorridor

@[expose] public section

namespace Skorokhod.PathClass.StepCorridor

/-- The finite-width cells are exactly the cells that contribute to the
`Hα` energy. Their common-partition rate sum is the real-valued energy. -/
theorem ContinuousAdmissibleStepCorridor.energy_toReal_eq_finiteCellRate
    (α : ℝ) (c : ContinuousAdmissibleStepCorridor) (hsep : TraceSeparated c.upper c.lower) :
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

/-- A finite partition rate converges as a common relative enlargement
vanishes. This is a deterministic continuity fact, independent of a process
law or an escape-rate hypothesis. -/
theorem tendsto_relativePartitionRate_vanishingEnlargement
    {α C : ℝ} {ι : Type*} (s : Finset ι) (energy : ι → ℝ) :
    Tendsto
      (fun ε : ℝ => C * (2 / (1 + ε)) ^ α * ∑ i ∈ s, energy i)
      (𝓝[>] (0 : ℝ))
      (𝓝 (C * 2 ^ α * ∑ i ∈ s, energy i)) := by
  have hid : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun ε : ℝ => 1 + ε) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.add hid
  have hratio : Tendsto (fun ε : ℝ => 2 / (1 + ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) := by
    have hnum : Tendsto (fun _ : ℝ => (2 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) := tendsto_const_nhds
    have hratio' := hnum.div hden one_ne_zero
    convert hratio' using 1 <;> ext ε <;> norm_num
  have hpow : Tendsto (fun ε : ℝ => (2 / (1 + ε)) ^ α)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 ^ α)) := by
    exact (Real.continuousAt_rpow_const 2 α
      (Or.inl (by norm_num : (2 : ℝ) ≠ 0))).tendsto.comp hratio
  have hconst : Tendsto (fun _ : ℝ => C)
      (𝓝[>] (0 : ℝ)) (𝓝 C) := tendsto_const_nhds
  have hscaled : Tendsto (fun ε : ℝ => C * (2 / (1 + ε)) ^ α)
      (𝓝[>] (0 : ℝ)) (𝓝 (C * 2 ^ α)) := hconst.mul hpow
  have henergy := hscaled.mul_const (∑ i ∈ s, energy i)
  simpa [mul_assoc] using henergy

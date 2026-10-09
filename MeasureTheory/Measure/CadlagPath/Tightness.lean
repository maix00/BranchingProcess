/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.Tight
public import MeasureTheory.Measure.Tight.Sequence
public import Topology.Cadlag.Skorokhod.Compactness.Billingsley
public import Topology.Cadlag.Skorokhod.Oscillation.Partition.Measurability
public import Topology.Cadlag.Range
public import Topology.Cadlag.Skorokhod.Range
public import Topology.Cadlag.Skorokhod.Topology

/-!
# Tightness criteria for càdlàg path laws

This file converts high-probability common compact range and oscillation
partition events into tightness of a family of laws on the Skorokhod path
space. It does not assume that the path space is Polish.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory

/-- A common compact range and a high-probability sequence of oscillation
partition events imply tightness of càdlàg path laws. The event hypothesis
controls all oscillation scales simultaneously, avoiding any assumption that
individual path laws are tight from a Polish-space theorem. -/
theorem isTightMeasureSet_of_compactRange_and_oscillationPartitions
    {I E : Type*} [MetricSpace E]
    (μ : I → Measure (CadlagPath unitInterval E))
    (hrange : ∀ η : ℝ≥0∞, 0 < η →
      ∃ range : Set E, IsCompact range ∧
        ∀ i, μ i (CadlagPath.rangeIn (T := unitInterval) range)ᶜ ≤ η)
    (hosc : ∀ η : ℝ≥0∞, 0 < η →
      ∃ gap oscillationTolerance : ℕ → ℝ,
        (∀ n, 0 < gap n) ∧ (∀ n, 0 < oscillationTolerance n) ∧
          Tendsto oscillationTolerance atTop (nhds 0) ∧
            ∀ i, μ i (Skorokhod.admitsOscillationPartitionSequence
              (E := E) gap oscillationTolerance)ᶜ ≤ η) :
    IsTightMeasureSet (Set.range μ) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro η hη
  have hhalf : 0 < η / 2 := ENNReal.div_pos (ne_of_gt hη) (by norm_num)
  obtain ⟨range, hrangeCompact, hrangeMass⟩ := hrange (η / 2) hhalf
  obtain ⟨gap, oscillationTolerance, hgap, htolerance, htendsto, hoscMass⟩ :=
    hosc (η / 2) hhalf
  let good : Set (CadlagPath unitInterval E) :=
    CadlagPath.rangeIn (T := unitInterval) range ∩
      Skorokhod.admitsOscillationPartitionSequence (E := E) gap oscillationTolerance
  have hpartitions : ∀ tolerance > 0, ∃ δ > 0, ∀ path ∈ good,
      ∃ partition : Skorokhod.OscillationPartition, δ < partition.mesh ∧
        ∃ oscillation < tolerance,
          Skorokhod.OscillationBoundedOnPartition partition path oscillation := by
    intro tolerance htolerance
    obtain ⟨n, hn⟩ := eventually_atTop.1 <|
      htendsto.eventually (Iio_mem_nhds htolerance)
    refine ⟨gap n, hgap n, ?_⟩
    intro path hpath
    have hlevel := Set.mem_iInter.mp hpath.2 n
    obtain ⟨partition, hmesh, oscillation, hoscillation, hbound⟩ := hlevel
    have hsmall : oscillationTolerance n < tolerance := hn n le_rfl
    exact ⟨partition, hmesh, oscillation,
      lt_trans hoscillation hsmall, hbound⟩
  obtain ⟨compact, hcompact, hgood⟩ :=
    Skorokhod.exists_isCompact_superset_of_uniform_admitsOscillationPartition
      ⟨range, hrangeCompact, fun path hpath t => hpath.1 t⟩ hpartitions
  refine ⟨compact, hcompact, ?_⟩
  intro ν hν
  obtain ⟨i, rfl⟩ := hν
  calc
    μ i compactᶜ ≤ μ i goodᶜ := measure_mono (compl_subset_compl.mpr hgood)
    _ ≤ μ i ((CadlagPath.rangeIn (T := unitInterval) range)ᶜ ∪
        (Skorokhod.admitsOscillationPartitionSequence
          (E := E) gap oscillationTolerance)ᶜ) := by
      apply measure_mono
      intro path hpath
      have hnot := hpath
      simp only [good, mem_compl_iff, mem_inter_iff] at hnot
      simp only [mem_union, mem_compl_iff]
      by_cases hrangePath : path ∈ CadlagPath.rangeIn (T := unitInterval) range
      · exact Or.inr (fun hoscPath => hnot ⟨hrangePath, hoscPath⟩)
      · exact Or.inl hrangePath
    _ ≤ μ i (CadlagPath.rangeIn (T := unitInterval) range)ᶜ +
        μ i (Skorokhod.admitsOscillationPartitionSequence
          (E := E) gap oscillationTolerance)ᶜ := measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add (hrangeMass i) (hoscMass i)
    _ = η := ENNReal.add_halves η

/-- Eventual compact-range and oscillation-partition probability bounds imply
tightness of càdlàg path laws when each exceptional law is tight individually.
The cutoff may depend on the requested error; the generic measure-space
criterion absorbs the resulting finite prefix without any Polish-space
instance on `CadlagPath`. -/
theorem isTightMeasureSet_range_of_eventually_compactRange_and_oscillationPartitions
    {E : Type*} [MetricSpace E]
    (μ : ℕ → Measure (CadlagPath unitInterval E))
    (hsingle : ∀ i, IsTightMeasureSet {μ i})
    (hrange : ∀ {η : ℝ≥0∞}, 0 < η →
      ∃ range : Set E, IsCompact range ∧
        ∀ᶠ i : ℕ in atTop, μ i (CadlagPath.rangeIn (T := unitInterval) range)ᶜ ≤ η)
    (hosc : ∀ {η : ℝ≥0∞}, 0 < η →
      ∃ gap oscillationTolerance : ℕ → ℝ,
        (∀ n, 0 < gap n) ∧ (∀ n, 0 < oscillationTolerance n) ∧
          Tendsto oscillationTolerance atTop (nhds 0) ∧
            ∀ᶠ i : ℕ in atTop, μ i (Skorokhod.admitsOscillationPartitionSequence
              (E := E) gap oscillationTolerance)ᶜ ≤ η) :
    IsTightMeasureSet (Set.range μ) := by
  apply MeasureTheory.isTightMeasureSet_range_of_eventually_uniform_compact_mass_bound
    μ hsingle
  intro η hη
  have hhalf : 0 < η / 2 := ENNReal.div_pos (ne_of_gt hη) (by norm_num)
  obtain ⟨range, hrangeCompact, hrangeMass⟩ := hrange hhalf
  obtain ⟨gap, oscillationTolerance, hgap, htolerance, htendsto, hoscMass⟩ :=
    hosc hhalf
  let oscillationEvent := Skorokhod.admitsOscillationPartitionSequence
    (E := E) gap oscillationTolerance
  have heventually : ∀ᶠ i : ℕ in atTop,
      μ i (CadlagPath.rangeIn (T := unitInterval) range)ᶜ ≤ η / 2 ∧
        μ i oscillationEventᶜ ≤ η / 2 := by
    filter_upwards [hrangeMass, hoscMass] with i hirange hiosc
    exact ⟨hirange, hiosc⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
  let good : Set (CadlagPath unitInterval E) :=
    CadlagPath.rangeIn (T := unitInterval) range ∩ oscillationEvent
  have hpartitions : ∀ tolerance > 0, ∃ δ > 0, ∀ path ∈ good,
      ∃ partition : Skorokhod.OscillationPartition, δ < partition.mesh ∧
        ∃ oscillation < tolerance,
          Skorokhod.OscillationBoundedOnPartition partition path oscillation := by
    intro tolerance htolerance'
    obtain ⟨n, hn⟩ := eventually_atTop.1 <|
      htendsto.eventually (Iio_mem_nhds htolerance')
    refine ⟨gap n, hgap n, ?_⟩
    intro path hpath
    have hlevel := Set.mem_iInter.mp hpath.2 n
    obtain ⟨partition, hmesh, oscillation, hoscillation, hbound⟩ := hlevel
    have hsmall : oscillationTolerance n < tolerance := hn n le_rfl
    exact ⟨partition, hmesh, oscillation,
      lt_trans hoscillation hsmall, hbound⟩
  obtain ⟨compact, hcompact, hgood⟩ :=
    Skorokhod.exists_isCompact_superset_of_uniform_admitsOscillationPartition
      ⟨range, hrangeCompact, fun path hpath t => hpath.1 t⟩ hpartitions
  refine ⟨N, compact, hcompact, ?_⟩
  intro i hi
  calc
    μ i compactᶜ ≤ μ i goodᶜ := measure_mono (compl_subset_compl.mpr hgood)
    _ ≤ μ i ((CadlagPath.rangeIn (T := unitInterval) range)ᶜ ∪ oscillationEventᶜ) := by
      apply measure_mono
      intro path hpath
      have hnot := hpath
      simp only [good, mem_compl_iff, mem_inter_iff] at hnot
      simp only [mem_union, mem_compl_iff]
      by_cases hrangePath : path ∈ CadlagPath.rangeIn (T := unitInterval) range
      · exact Or.inr (fun hoscPath => hnot ⟨hrangePath, hoscPath⟩)
      · exact Or.inl hrangePath
    _ ≤ μ i (CadlagPath.rangeIn (T := unitInterval) range)ᶜ + μ i oscillationEventᶜ :=
      measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add (hN i hi).1 (hN i hi).2
    _ = η := ENNReal.add_halves η

end MeasureTheory

end

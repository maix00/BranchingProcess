/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.ContinuousBoundary
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.SourcePath

/-!
# Measurability of source random-walk continuous-corridor events

The source path has finitely many constant time cells. A continuous boundary
may approach the value on a cell as time approaches the cell's excluded right
endpoint, so strict corridor membership need not give a uniform margin on the
whole cell. This file exhausts each half-open cell by compact subintervals;
the resulting countable family of finite-coordinate conditions proves
measurability while retaining the `S_(n-1)` terminal convention.
-/

open MeasureTheory
open Filter
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Skorokhod
open Skorokhod.PathClass.StepCorridor

/-- A compact truncation of the `j`th source step cell. The right endpoint is
approached from below, so the path keeps the value of its `j`th partial sum
throughout this interval. -/
noncomputable def sourceContinuousBoundaryCellCutoff
    (n : ℕ) (hn : 0 < n) (j : Fin n) (m : ℕ) : unitInterval := by
  let left := uniformGridTime n hn j.castSucc
  let right := uniformGridSuccessorTime n hn j
  refine ⟨(right : ℝ) - 1 / ((n + m + 1 : ℕ) : ℝ), ?_⟩
  constructor
  · have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hden : 0 < ((n + m + 1 : ℕ) : ℝ) := by positivity
    have hrec : 1 / ((n + m + 1 : ℕ) : ℝ) ≤ 1 / (n : ℝ) := by
      apply one_div_le_one_div_of_le hnReal
      exact_mod_cast (show n ≤ n + m + 1 by omega)
    have hleft : (left : ℝ) = (j : ℝ) / n := by
      simp [left, uniformGridTime_val]
    have hright : (right : ℝ) = ((j : ℝ) + 1) / n := by
      simp [right, uniformGridSuccessorTime_val]
    change 0 ≤ (right : ℝ) - 1 / ((n + m + 1 : ℕ) : ℝ)
    rw [hright]
    have hgap : ((j : ℝ) + 1) / n - (j : ℝ) / n = 1 / n := by
      field_simp
      ring
    have hjnonneg : 0 ≤ (j : ℝ) / n := div_nonneg (Nat.cast_nonneg _) hnReal.le
    nlinarith
  · have hden : 0 < ((n + m + 1 : ℕ) : ℝ) := by positivity
    have hright := (uniformGridSuccessorTime n hn j).property.2
    have hlt : (right : ℝ) - 1 / ((n + m + 1 : ℕ) : ℝ) < (right : ℝ) :=
      sub_lt_self _ (one_div_pos.mpr hden)
    exact le_trans (le_of_lt hlt) hright

@[simp]
theorem sourceContinuousBoundaryCellCutoff_val
    (n : ℕ) (hn : 0 < n) (j : Fin n) (m : ℕ) :
    (sourceContinuousBoundaryCellCutoff n hn j m : ℝ) =
      (uniformGridSuccessorTime n hn j : ℝ) -
        1 / ((n + m + 1 : ℕ) : ℝ) := rfl

theorem uniformGridTime_le_sourceContinuousBoundaryCellCutoff
    (n : ℕ) (hn : 0 < n) (j : Fin n) (m : ℕ) :
    uniformGridTime n hn j.castSucc ≤
      sourceContinuousBoundaryCellCutoff n hn j m := by
  apply Subtype.mk_le_mk.mpr
  change (uniformGridTime n hn j.castSucc : ℝ) ≤
    (uniformGridSuccessorTime n hn j : ℝ) -
      1 / ((n + m + 1 : ℕ) : ℝ)
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < ((n + m + 1 : ℕ) : ℝ) := by positivity
  have hrec : 1 / ((n + m + 1 : ℕ) : ℝ) ≤ 1 / (n : ℝ) := by
    apply one_div_le_one_div_of_le hnReal
    exact_mod_cast (show n ≤ n + m + 1 by omega)
  have hleft : (uniformGridTime n hn j.castSucc : ℝ) = (j : ℝ) / n := by
    simp [uniformGridTime_val]
  have hright : (uniformGridSuccessorTime n hn j : ℝ) =
      ((j : ℝ) + 1) / n := by
    simp [uniformGridSuccessorTime_val]
  rw [hleft, hright]
  have hgap : ((j : ℝ) + 1) / n - (j : ℝ) / n = 1 / n := by
    field_simp
    ring
  nlinarith

theorem sourceContinuousBoundaryCellCutoff_lt_right
    (n : ℕ) (hn : 0 < n) (j : Fin n) (m : ℕ) :
    sourceContinuousBoundaryCellCutoff n hn j m <
      uniformGridSuccessorTime n hn j := by
  apply Subtype.mk_lt_mk.mpr
  change (uniformGridSuccessorTime n hn j : ℝ) -
    1 / ((n + m + 1 : ℕ) : ℝ) <
      (uniformGridSuccessorTime n hn j : ℝ)
  have hden : 0 < ((n + m + 1 : ℕ) : ℝ) := by positivity
  linarith [one_div_pos.mpr hden]

/-- The scaled partial sum carried by one source step cell. -/
noncomputable def sourceNormalizedStepCellValue (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) (j : Fin n) : ℝ :=
  (scale n)⁻¹ * AdditivePath.displacement (j : ℕ) increment

private theorem sourceNormalizedStepCadlagPathIcc_eq_cellValue_of_mem_cell
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (increment : ℕ → ℝ)
    (j : Fin n) (m : ℕ) {t : unitInterval}
    (ht : t ∈ Set.Icc (uniformGridTime n hn j.castSucc)
      (sourceContinuousBoundaryCellCutoff n hn j m)) :
    sourceNormalizedStepCadlagPathIcc scale n increment t =
      sourceNormalizedStepCellValue scale n increment j := by
  have hcutRight := sourceContinuousBoundaryCellCutoff_lt_right n hn j m
  have htltRight : t < uniformGridSuccessorTime n hn j := lt_of_le_of_lt ht.2 hcutRight
  have htltTop : t < ⊤ := htltRight.trans_le le_top
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hleftVal : (uniformGridTime n hn j.castSucc : ℝ) = (j : ℝ) / n := by
    simp [uniformGridTime_val]
  have hrightVal : (uniformGridSuccessorTime n hn j : ℝ) =
      ((j : ℝ) + 1) / n := by
    simp [uniformGridSuccessorTime_val]
  have hfloorLow : (j : ℝ) ≤ (n : ℝ) * (t : ℝ) := by
    have h := Subtype.mk_le_mk.mp ht.1
    change (uniformGridTime n hn j.castSucc : ℝ) ≤ (t : ℝ) at h
    rw [hleftVal] at h
    simpa [mul_comm] using (div_le_iff₀ hnReal).1 h
  have hfloorHigh : (n : ℝ) * (t : ℝ) < (j : ℝ) + 1 := by
    have h : (t : ℝ) < (uniformGridSuccessorTime n hn j : ℝ) :=
      Subtype.mk_lt_mk.mp htltRight
    rw [hrightVal] at h
    simpa [mul_comm] using (lt_div_iff₀ hnReal).1 h
  have hnonneg : 0 ≤ (n : ℝ) * (t : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) t.property.1
  have hfloor : ⌊(n : ℝ) * (t : ℝ)⌋₊ = j.val :=
    (Nat.floor_eq_iff hnonneg).2 ⟨hfloorLow, hfloorHigh⟩
  have htne : t ≠ ⊤ := ne_of_lt htltTop
  rw [sourceNormalizedStepCadlagPathIcc_apply_of_ne_top scale n increment htne,
    normalizedStepPath, hfloor]
  rfl

/-- Strict continuous-boundary membership on all compact truncations of the
source step cells. -/
def sourceContinuousBoundaryCellConditions
    (lower upper : C(unitInterval, ℝ)) (scale : ℕ → ℝ)
    (n : ℕ) (hn : 0 < n) (increment : ℕ → ℝ) : Prop :=
  ∀ j : Fin n, ∀ m : ℕ, ∀ t ∈ Set.Icc (uniformGridTime n hn j.castSucc)
      (sourceContinuousBoundaryCellCutoff n hn j m),
    lower t < sourceNormalizedStepCellValue scale n increment j ∧
      sourceNormalizedStepCellValue scale n increment j < upper t

private theorem isOpen_set_strictly_between_on_compact
    {K : Set unitInterval} (hK : IsCompact K) (hne : K.Nonempty)
    (lower upper : C(unitInterval, ℝ)) :
    IsOpen {x : ℝ | ∀ t ∈ K, lower t < x ∧ x < upper t} := by
  obtain ⟨tl, htl, hmax⟩ := hK.exists_isMaxOn hne lower.continuous.continuousOn
  obtain ⟨tu, htu, hmin⟩ := hK.exists_isMinOn hne upper.continuous.continuousOn
  have heq : {x : ℝ | ∀ t ∈ K, lower t < x ∧ x < upper t} =
      Set.Ioi (lower tl) ∩ Set.Iio (upper tu) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · intro hx
      exact ⟨(hx tl htl).1, (hx tu htu).2⟩
    · rintro ⟨hxl, hxu⟩
      intro t ht
      exact ⟨lt_of_le_of_lt (hmax ht) hxl,
        lt_of_lt_of_le hxu (hmin ht)⟩
  rw [heq]
  exact isOpen_Ioi.inter isOpen_Iio

private theorem measurableSet_sourceContinuousBoundaryCellCondition
    (lower upper : C(unitInterval, ℝ)) (scale : ℕ → ℝ)
    (n : ℕ) (hn : 0 < n) (j : Fin n) (m : ℕ) :
    MeasurableSet {increment : ℕ → ℝ |
      ∀ t ∈ Set.Icc (uniformGridTime n hn j.castSucc)
          (sourceContinuousBoundaryCellCutoff n hn j m),
        lower t < sourceNormalizedStepCellValue scale n increment j ∧
          sourceNormalizedStepCellValue scale n increment j < upper t} := by
  let K : Set unitInterval := Set.Icc (uniformGridTime n hn j.castSucc)
    (sourceContinuousBoundaryCellCutoff n hn j m)
  have hK : IsCompact K := by
    dsimp [K]
    exact isCompact_Icc
  have hne : K.Nonempty := by
    refine ⟨uniformGridTime n hn j.castSucc, ?_⟩
    constructor
    · rfl
    · exact uniformGridTime_le_sourceContinuousBoundaryCellCutoff n hn j m
  have hopen : IsOpen {x : ℝ | ∀ t ∈ K, lower t < x ∧ x < upper t} :=
    isOpen_set_strictly_between_on_compact hK hne lower upper
  have hvalue : Measurable (fun increment : ℕ → ℝ =>
      sourceNormalizedStepCellValue scale n increment j) := by
    exact measurable_const.mul (displacement_measurable (j : ℕ))
  have hpreimage := hopen.measurableSet.preimage hvalue
  simpa [K, sourceNormalizedStepCellValue] using hpreimage

theorem measurableSet_sourceContinuousBoundaryCellConditions
    (lower upper : C(unitInterval, ℝ)) (scale : ℕ → ℝ)
    (n : ℕ) (hn : 0 < n) :
    MeasurableSet {increment : ℕ → ℝ |
      sourceContinuousBoundaryCellConditions lower upper scale n hn increment} := by
  rw [show {increment : ℕ → ℝ |
      sourceContinuousBoundaryCellConditions lower upper scale n hn increment} =
      ⋂ j : Fin n, ⋂ m : ℕ,
        {increment : ℕ → ℝ |
          ∀ t ∈ Set.Icc (uniformGridTime n hn j.castSucc)
              (sourceContinuousBoundaryCellCutoff n hn j m),
            lower t < sourceNormalizedStepCellValue scale n increment j ∧
              sourceNormalizedStepCellValue scale n increment j < upper t} by
    ext increment
    simp [sourceContinuousBoundaryCellConditions]]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun m =>
    measurableSet_sourceContinuousBoundaryCellCondition lower upper scale n hn j m

private theorem measurableSet_sourceContinuousBoundaryTopCondition
    (lower upper : C(unitInterval, ℝ)) (scale : ℕ → ℝ)
    {n : ℕ} :
    MeasurableSet {increment : ℕ → ℝ |
      lower ⊤ < (scale n)⁻¹ * AdditivePath.displacement (n - 1) increment ∧
        (scale n)⁻¹ * AdditivePath.displacement (n - 1) increment < upper ⊤} := by
  have hvalue : Measurable (fun increment : ℕ → ℝ =>
      (scale n)⁻¹ * AdditivePath.displacement (n - 1) increment) :=
    measurable_const.mul (displacement_measurable (n - 1))
  exact (measurableSet_Ioi.preimage hvalue).inter
    (measurableSet_Iio.preimage hvalue)

theorem sourceNormalizedStepCadlagPathIcc_mem_relativeContinuousBoundaryCorridorSet_iff
    (lower upper : C(unitInterval, ℝ)) (scale : ℕ → ℝ)
    {n : ℕ} (hn : 0 < n) (increment : ℕ → ℝ) :
    sourceNormalizedStepCadlagPathIcc scale n increment ∈
      relativeContinuousBoundaryCorridorSet lower upper ↔
    sourceContinuousBoundaryCellConditions lower upper scale n hn increment ∧
      lower ⊤ < (scale n)⁻¹ * AdditivePath.displacement (n - 1) increment ∧
        (scale n)⁻¹ * AdditivePath.displacement (n - 1) increment < upper ⊤ := by
  let path := sourceNormalizedStepCadlagPathIcc scale n increment
  let last : Fin n := ⟨n - 1, by omega⟩
  constructor
  · intro hpath
    change path ∈ terminalLeftPathSpace ∧ path ∈ continuousBoundaryCorridorSet lower upper at hpath
    rcases hpath.2 with ⟨hzero, hbetween⟩
    refine ⟨?_, ?_⟩
    · intro j m t ht
      have hval := sourceNormalizedStepCadlagPathIcc_eq_cellValue_of_mem_cell
        scale hn increment j m ht
      have hbetween' := hbetween t
      change lower t < sourceNormalizedStepCadlagPathIcc scale n increment t ∧
        sourceNormalizedStepCadlagPathIcc scale n increment t < upper t at hbetween'
      rw [hval] at hbetween'
      exact hbetween'
    · have htop := hbetween ⊤
      rw [sourceNormalizedStepCadlagPathIcc_apply_top scale hn increment] at htop
      simpa [last, sourceNormalizedStepCellValue] using htop
  · rintro ⟨hcell, htopLower, htopUpper⟩
    refine ⟨terminalLeftPath_mem_space (normalizedStepCadlagPathIcc scale n increment), ?_⟩
    change path ⊥ = 0 ∧ ∀ t : unitInterval,
      lower t < path t ∧ path t < upper t
    constructor
    · have hbotne : (⊥ : unitInterval) ≠ ⊤ := by norm_num [unitInterval]
      rw [sourceNormalizedStepCadlagPathIcc_apply_of_ne_top scale n increment hbotne]
      simp [normalizedStepPath]
    · intro t
      by_cases htop : t = ⊤
      · subst t
        rw [sourceNormalizedStepCadlagPathIcc_apply_top scale hn increment]
        exact ⟨htopLower, htopUpper⟩
      · have htval : (t : ℝ) < 1 := by
          have httop : t < (⊤ : unitInterval) := lt_of_le_of_ne le_top htop
          exact Subtype.mk_lt_mk.mp httop
        have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
        have hnonneg : 0 ≤ (n : ℝ) * (t : ℝ) :=
          mul_nonneg (Nat.cast_nonneg _) t.property.1
        have hntlt : (n : ℝ) * (t : ℝ) < n := by
          exact (mul_lt_mul_of_pos_left htval hnReal).trans_eq (by ring)
        let k : ℕ := ⌊(n : ℝ) * (t : ℝ)⌋₊
        have hklt : k < n := by
          dsimp [k]
          exact (Nat.floor_lt hnonneg).2 hntlt
        let j : Fin n := ⟨k, hklt⟩
        have hfloorLow : (k : ℝ) ≤ (n : ℝ) * (t : ℝ) := Nat.floor_le hnonneg
        have hfloorHigh : (n : ℝ) * (t : ℝ) < (k : ℝ) + 1 := by
          simpa [k, Nat.cast_add] using Nat.lt_succ_floor ((n : ℝ) * (t : ℝ))
        have hleft : uniformGridTime n hn j.castSucc ≤ t := by
          apply Subtype.mk_le_mk.mpr
          change (uniformGridTime n hn j.castSucc : ℝ) ≤ (t : ℝ)
          have hgrid : (uniformGridTime n hn j.castSucc : ℝ) = (k : ℝ) / n := by
            simp [uniformGridTime_val, j]
          rw [hgrid]
          exact (div_le_iff₀ hnReal).2 (by simpa [mul_comm, j] using hfloorLow)
        have hright : (t : ℝ) < (uniformGridSuccessorTime n hn j : ℝ) := by
          have hgrid : (uniformGridSuccessorTime n hn j : ℝ) =
              ((k : ℝ) + 1) / n := by
            simp [uniformGridSuccessorTime_val, j]
          rw [hgrid]
          exact (lt_div_iff₀ hnReal).2 (by simpa [mul_comm, j] using hfloorHigh)
        have hgap : 0 < (uniformGridSuccessorTime n hn j : ℝ) - (t : ℝ) :=
          sub_pos.mpr hright
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hgap
        have hmden : 1 / ((n + m + 1 : ℕ) : ℝ) ≤ 1 / ((m : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast (show m + 1 ≤ n + m + 1 by omega)
        have hcut : t ≤ sourceContinuousBoundaryCellCutoff n hn j m := by
          apply Subtype.mk_le_mk.mpr
          exact le_of_lt (by linarith [hmden.trans_lt hm])
        have hcellMem : t ∈ Set.Icc (uniformGridTime n hn j.castSucc)
            (sourceContinuousBoundaryCellCutoff n hn j m) := ⟨hleft, hcut⟩
        have hbounds := hcell j m t hcellMem
        rw [sourceNormalizedStepCadlagPathIcc_eq_cellValue_of_mem_cell
          scale hn increment j m hcellMem]
        exact hbounds

/-- The exact source-path corridor event is measurable. Compact truncations
of each half-open step cell retain all strict inequalities, including cases
where a continuous boundary is approached at the excluded right endpoint.
The terminal endpoint uses the source value `S_(n-1)`. -/
private theorem measurableSet_sourceNormalizedStepCadlagPathIcc_preimage_relativeContinuousBoundaryCorridorSet_of_pos
    (lower upper : C(unitInterval, ℝ)) (scale : ℕ → ℝ)
    {n : ℕ} (hn : 0 < n) :
    MeasurableSet {increment : ℕ → ℝ |
      sourceNormalizedStepCadlagPathIcc scale n increment ∈
        relativeContinuousBoundaryCorridorSet lower upper} := by
  rw [show {increment : ℕ → ℝ |
      sourceNormalizedStepCadlagPathIcc scale n increment ∈
        relativeContinuousBoundaryCorridorSet lower upper} =
      {increment | sourceContinuousBoundaryCellConditions lower upper scale n hn increment} ∩
        {increment | lower ⊤ < (scale n)⁻¹ *
            AdditivePath.displacement (n - 1) increment ∧
          (scale n)⁻¹ * AdditivePath.displacement (n - 1) increment < upper ⊤} by
    ext increment
    exact (sourceNormalizedStepCadlagPathIcc_mem_relativeContinuousBoundaryCorridorSet_iff
      lower upper scale hn increment)]
  exact (measurableSet_sourceContinuousBoundaryCellConditions lower upper scale n hn).inter
    (measurableSet_sourceContinuousBoundaryTopCondition lower upper scale)

private theorem sourceNormalizedStepCadlagPathIcc_zero
    (scale : ℕ → ℝ) (increment : ℕ → ℝ) (t : unitInterval) :
    sourceNormalizedStepCadlagPathIcc scale 0 increment t = 0 := by
  by_cases ht : t = ⊤
  · subst t
    rw [sourceNormalizedStepCadlagPathIcc, terminalLeftPath_apply_top]
    have hconst : ∀ s : unitInterval,
        normalizedStepCadlagPathIcc scale 0 increment s = 0 := by
      intro s
      simp [normalizedStepCadlagPathIcc_apply, normalizedStepPath]
    have hbotTop : (⊥ : unitInterval) < ⊤ := by norm_num [unitInterval]
    have hleft : Function.leftLim
        (fun s : unitInterval => normalizedStepCadlagPathIcc scale 0 increment s) ⊤ = 0 :=
      leftLim_eq_of_tendsto
        (h := nhdsLT_neBot_of_exists_lt ⟨⊥, hbotTop⟩)
        (by simpa only [hconst] using
          (tendsto_const_nhds : Tendsto (fun _ : unitInterval => (0 : ℝ))
            (𝓝[<] ⊤) (𝓝 0)))
    exact hleft
  · rw [sourceNormalizedStepCadlagPathIcc_apply_of_ne_top scale 0 increment ht]
    simp [normalizedStepPath]

/-- For every number of steps, including zero, the exact continuous-corridor
preimage on the canonical increment space is measurable. -/
theorem measurableSet_sourceNormalizedStepCadlagPathIcc_preimage_relativeContinuousBoundaryCorridorSet
    (lower upper : C(unitInterval, ℝ)) (scale : ℕ → ℝ) (n : ℕ) :
    MeasurableSet {increment : ℕ → ℝ |
      sourceNormalizedStepCadlagPathIcc scale n increment ∈
        relativeContinuousBoundaryCorridorSet lower upper} := by
  by_cases hn : 0 < n
  · exact measurableSet_sourceNormalizedStepCadlagPathIcc_preimage_relativeContinuousBoundaryCorridorSet_of_pos
      lower upper scale hn
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    by_cases hcorridor : ∀ t : unitInterval, lower t < 0 ∧ 0 < upper t
    · have heq : {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale 0 increment ∈
            relativeContinuousBoundaryCorridorSet lower upper} = Set.univ := by
        ext increment
        constructor
        · intro _
          exact Set.mem_univ _
        · intro _
          refine ⟨terminalLeftPath_mem_space
            (normalizedStepCadlagPathIcc scale 0 increment), ?_⟩
          refine ⟨?_, ?_⟩
          · simp only [sourceNormalizedStepCadlagPathIcc_zero]
          · intro t
            simpa only [sourceNormalizedStepCadlagPathIcc_zero] using hcorridor t
      rw [heq]
      exact MeasurableSet.univ
    · have heq : {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale 0 increment ∈
            relativeContinuousBoundaryCorridorSet lower upper} = ∅ := by
        ext increment
        constructor
        · intro hpath
          change sourceNormalizedStepCadlagPathIcc scale 0 increment ∈
            terminalLeftPathSpace ∧
              sourceNormalizedStepCadlagPathIcc scale 0 increment ∈
                continuousBoundaryCorridorSet lower upper at hpath
          rcases hpath.2 with ⟨_, hbetween⟩
          apply hcorridor
          intro t
          simpa only [sourceNormalizedStepCadlagPathIcc_zero] using hbetween t
        · simp
      rw [heq]
      exact MeasurableSet.empty

end ProbabilityTheory.RandomWalk

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.ContinuousBoundary
import Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft.Basic

/-!
# Internal lemmas for terminal-left continuous-boundary events

This module contains the non-reusable construction and measurability steps for
`ProbabilityTheory.RandomWalk.measurableSet_terminalLeftNormalizedStepCadlagPathIcc_preimage_relativeContinuousBoundaryCorridorSet`.

## Internal proof declarations

- `terminalLeftContinuousBoundaryCellCutoff` defines the compact right-end
  approximation $b_{j,m}=(j+1)/n-1/(n+m+1)$ of the $j$th step cell.
- `terminalLeftNormalizedStepCellValue` is the scaled partial sum
  $\operatorname{scale}(n)^{-1} S_j$ carried by that cell.
- `terminalLeftContinuousBoundaryCellConditions` requires the carried value
  to lie strictly between the continuous boundaries on every compact cell
  $[j/n,b_{j,m}]$.
- `measurableSet_terminalLeftNormalizedStepCadlagPathIcc_preimage_relativeContinuousBoundaryCorridorSet_of_pos`
  proves measurability of the exact terminal-left corridor event when $n>0$.
- `terminalLeftNormalizedStepCadlagPathIcc_zero` identifies the terminal-left
  path with the zero path when $n=0$.
-/

open MeasureTheory
open Filter
open scoped Topology

namespace ProbabilityTheory.RandomWalk

open Skorokhod
open Skorokhod.PathClass.StepCorridor

/-- A compact truncation of the `j`th terminal-left step cell. The right endpoint
is approached from below, so the path keeps the value of its `j`th partial sum
throughout this interval. Its value is
$(j+1)/n-1/(n+m+1)$. -/
noncomputable def terminalLeftContinuousBoundaryCellCutoff
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

private lemma uniformGridTime_le_terminalLeftContinuousBoundaryCellCutoff
    (n : ℕ) (hn : 0 < n) (j : Fin n) (m : ℕ) :
    uniformGridTime n hn j.castSucc ≤
      terminalLeftContinuousBoundaryCellCutoff n hn j m := by
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

private lemma terminalLeftContinuousBoundaryCellCutoff_lt_right
    (n : ℕ) (hn : 0 < n) (j : Fin n) (m : ℕ) :
    terminalLeftContinuousBoundaryCellCutoff n hn j m <
      uniformGridSuccessorTime n hn j := by
  apply Subtype.mk_lt_mk.mpr
  change (uniformGridSuccessorTime n hn j : ℝ) -
    1 / ((n + m + 1 : ℕ) : ℝ) <
      (uniformGridSuccessorTime n hn j : ℝ)
  have hden : 0 < ((n + m + 1 : ℕ) : ℝ) := by positivity
  linarith [one_div_pos.mpr hden]

/-- The scaled partial sum carried by one terminal-left step cell:
`scale n`⁻¹ times the `j`th partial sum. -/
noncomputable def terminalLeftNormalizedStepCellValue (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) (j : Fin n) : ℝ :=
  (scale n)⁻¹ * AdditivePath.displacement (j : ℕ) increment

private lemma terminalLeftNormalizedStepCadlagPathIcc_eq_cellValue_of_mem_cell
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (increment : ℕ → ℝ)
    (j : Fin n) (m : ℕ) {t : unitInterval}
    (ht : t ∈ Set.Icc (uniformGridTime n hn j.castSucc)
      (terminalLeftContinuousBoundaryCellCutoff n hn j m)) :
    terminalLeftNormalizedStepCadlagPathIcc scale n increment t =
      terminalLeftNormalizedStepCellValue scale n increment j := by
  have hcutRight := terminalLeftContinuousBoundaryCellCutoff_lt_right n hn j m
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
  rw [terminalLeftNormalizedStepCadlagPathIcc_apply_of_ne_top scale n increment htne,
    normalizedStepPath, hfloor]
  rfl

/-- Every compact truncation of every terminal-left step cell satisfies the
strict continuous-boundary inequalities. -/
def terminalLeftContinuousBoundaryCellConditions
    (lower upper : C(unitInterval, ℝ)) (scale : ℕ → ℝ)
    (n : ℕ) (hn : 0 < n) (increment : ℕ → ℝ) : Prop :=
  ∀ j : Fin n, ∀ m : ℕ, ∀ t ∈ Set.Icc (uniformGridTime n hn j.castSucc)
      (terminalLeftContinuousBoundaryCellCutoff n hn j m),
    lower t < terminalLeftNormalizedStepCellValue scale n increment j ∧
      terminalLeftNormalizedStepCellValue scale n increment j < upper t

private lemma isOpen_set_strictly_between_on_compact
    {K : Set unitInterval} (hK : IsCompact K) (hne : K.Nonempty)
    (lower upper : C(unitInterval, ℝ)) :
    IsOpen {x : ℝ | ∀ t ∈ K, lower t < x ∧ x < upper t} := by
  have heq : {x : ℝ | ∀ t ∈ K, lower t < x ∧ x < upper t} =
      Set.Ioi (sSup (lower '' K)) ∩ Set.Iio (sInf (upper '' K)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · exact (hK.sSup_lt_iff_of_continuous hne
          lower.continuous.continuousOn x).2 (fun t ht => (hx t ht).1)
      · exact (hK.lt_sInf_iff_of_continuous hne
          upper.continuous.continuousOn x).2 (fun t ht => (hx t ht).2)
    · rintro ⟨hxl, hxu⟩
      intro t ht
      exact ⟨(hK.sSup_lt_iff_of_continuous hne
          lower.continuous.continuousOn x).1 hxl t ht,
        (hK.lt_sInf_iff_of_continuous hne
          upper.continuous.continuousOn x).1 hxu t ht⟩
  rw [heq]
  exact isOpen_Ioi.inter isOpen_Iio

private lemma measurableSet_terminalLeftContinuousBoundaryCellCondition
    (lower upper : C(unitInterval, ℝ)) (scale : ℕ → ℝ)
    (n : ℕ) (hn : 0 < n) (j : Fin n) (m : ℕ) :
    MeasurableSet {increment : ℕ → ℝ |
      ∀ t ∈ Set.Icc (uniformGridTime n hn j.castSucc)
          (terminalLeftContinuousBoundaryCellCutoff n hn j m),
        lower t < terminalLeftNormalizedStepCellValue scale n increment j ∧
          terminalLeftNormalizedStepCellValue scale n increment j < upper t} := by
  let K : Set unitInterval := Set.Icc (uniformGridTime n hn j.castSucc)
    (terminalLeftContinuousBoundaryCellCutoff n hn j m)
  have hK : IsCompact K := by
    dsimp [K]
    exact isCompact_Icc
  have hne : K.Nonempty := by
    refine ⟨uniformGridTime n hn j.castSucc, ?_⟩
    constructor
    · rfl
    · exact uniformGridTime_le_terminalLeftContinuousBoundaryCellCutoff n hn j m
  have hopen : IsOpen {x : ℝ | ∀ t ∈ K, lower t < x ∧ x < upper t} :=
    isOpen_set_strictly_between_on_compact hK hne lower upper
  have hvalue : Measurable (fun increment : ℕ → ℝ =>
      terminalLeftNormalizedStepCellValue scale n increment j) := by
    exact measurable_const.mul (displacement_measurable (j : ℕ))
  have hpreimage := hopen.measurableSet.preimage hvalue
  simpa [K, terminalLeftNormalizedStepCellValue] using hpreimage

private lemma measurableSet_terminalLeftContinuousBoundaryCellConditions
    (lower upper : C(unitInterval, ℝ)) (scale : ℕ → ℝ)
    (n : ℕ) (hn : 0 < n) :
    MeasurableSet {increment : ℕ → ℝ |
      terminalLeftContinuousBoundaryCellConditions lower upper scale n hn increment} := by
  rw [show {increment : ℕ → ℝ |
      terminalLeftContinuousBoundaryCellConditions lower upper scale n hn increment} =
      ⋂ j : Fin n, ⋂ m : ℕ,
        {increment : ℕ → ℝ |
          ∀ t ∈ Set.Icc (uniformGridTime n hn j.castSucc)
              (terminalLeftContinuousBoundaryCellCutoff n hn j m),
            lower t < terminalLeftNormalizedStepCellValue scale n increment j ∧
              terminalLeftNormalizedStepCellValue scale n increment j < upper t} by
    ext increment
    simp [terminalLeftContinuousBoundaryCellConditions]]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun m =>
    measurableSet_terminalLeftContinuousBoundaryCellCondition lower upper scale n hn j m

private lemma measurableSet_terminalLeftContinuousBoundaryTopCondition
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

private lemma terminalLeftNormalizedStepCadlagPathIcc_mem_relativeContinuousBoundaryCorridorSet_iff
    (lower upper : C(unitInterval, ℝ)) (scale : ℕ → ℝ)
    {n : ℕ} (hn : 0 < n) (increment : ℕ → ℝ) :
    terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
      relativeContinuousBoundaryCorridorSet lower upper ↔
    terminalLeftContinuousBoundaryCellConditions lower upper scale n hn increment ∧
      lower ⊤ < (scale n)⁻¹ * AdditivePath.displacement (n - 1) increment ∧
        (scale n)⁻¹ * AdditivePath.displacement (n - 1) increment < upper ⊤ := by
  let path := terminalLeftNormalizedStepCadlagPathIcc scale n increment
  let last : Fin n := ⟨n - 1, by omega⟩
  constructor
  · intro hpath
    change path ∈ terminalLeftPathSpace ∧ path ∈ continuousBoundaryCorridorSet lower upper at hpath
    rcases hpath.2 with ⟨hzero, hbetween⟩
    refine ⟨?_, ?_⟩
    · intro j m t ht
      have hval := terminalLeftNormalizedStepCadlagPathIcc_eq_cellValue_of_mem_cell
        scale hn increment j m ht
      have hbetween' := hbetween t
      change lower t < terminalLeftNormalizedStepCadlagPathIcc scale n increment t ∧
        terminalLeftNormalizedStepCadlagPathIcc scale n increment t < upper t at hbetween'
      rw [hval] at hbetween'
      exact hbetween'
    · have htop := hbetween ⊤
      rw [terminalLeftNormalizedStepCadlagPathIcc_apply_top scale hn increment] at htop
      simpa [last, terminalLeftNormalizedStepCellValue] using htop
  · rintro ⟨hcell, htopLower, htopUpper⟩
    refine ⟨terminalLeftPath_mem_space (normalizedStepCadlagPathIcc scale n increment), ?_⟩
    change path ⊥ = 0 ∧ ∀ t : unitInterval,
      lower t < path t ∧ path t < upper t
    constructor
    · have hbotne : (⊥ : unitInterval) ≠ ⊤ := by norm_num [unitInterval]
      rw [terminalLeftNormalizedStepCadlagPathIcc_apply_of_ne_top scale n increment hbotne]
      simp [normalizedStepPath]
    · intro t
      by_cases htop : t = ⊤
      · subst t
        rw [terminalLeftNormalizedStepCadlagPathIcc_apply_top scale hn increment]
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
        have hcut : t ≤ terminalLeftContinuousBoundaryCellCutoff n hn j m := by
          apply Subtype.mk_le_mk.mpr
          exact le_of_lt (by linarith [hmden.trans_lt hm])
        have hcellMem : t ∈ Set.Icc (uniformGridTime n hn j.castSucc)
            (terminalLeftContinuousBoundaryCellCutoff n hn j m) := ⟨hleft, hcut⟩
        have hbounds := hcell j m t hcellMem
        rw [terminalLeftNormalizedStepCadlagPathIcc_eq_cellValue_of_mem_cell
          scale hn increment j m hcellMem]
        exact hbounds

/-- The exact terminal-left path corridor event is measurable. Compact truncations
of each half-open step cell retain all strict inequalities, including cases
where a continuous boundary is approached at the excluded right endpoint.
The terminal endpoint uses the terminal-left value `S_(n-1)`. -/
lemma measurableSet_terminalLeftNormalizedStepCadlagPathIcc_preimage_relativeContinuousBoundaryCorridorSet_of_pos
    (lower upper : C(unitInterval, ℝ)) (scale : ℕ → ℝ)
    {n : ℕ} (hn : 0 < n) :
    MeasurableSet {increment : ℕ → ℝ |
      terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
        relativeContinuousBoundaryCorridorSet lower upper} := by
  rw [show {increment : ℕ → ℝ |
      terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
        relativeContinuousBoundaryCorridorSet lower upper} =
      {increment | terminalLeftContinuousBoundaryCellConditions lower upper scale n hn increment} ∩
        {increment | lower ⊤ < (scale n)⁻¹ *
            AdditivePath.displacement (n - 1) increment ∧
          (scale n)⁻¹ * AdditivePath.displacement (n - 1) increment < upper ⊤} by
    ext increment
    exact (terminalLeftNormalizedStepCadlagPathIcc_mem_relativeContinuousBoundaryCorridorSet_iff
      lower upper scale hn increment)]
  exact (measurableSet_terminalLeftContinuousBoundaryCellConditions lower upper scale n hn).inter
    (measurableSet_terminalLeftContinuousBoundaryTopCondition lower upper scale)

/-- The terminal-left modification of the zero-step path is identically zero. -/
lemma terminalLeftNormalizedStepCadlagPathIcc_zero
    (scale : ℕ → ℝ) (increment : ℕ → ℝ) (t : unitInterval) :
    terminalLeftNormalizedStepCadlagPathIcc scale 0 increment t = 0 := by
  by_cases ht : t = ⊤
  · subst t
    rw [terminalLeftNormalizedStepCadlagPathIcc, terminalLeftPath_apply_top]
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
  · rw [terminalLeftNormalizedStepCadlagPathIcc_apply_of_ne_top scale 0 increment ht]
    simp [normalizedStepPath]


end ProbabilityTheory.RandomWalk

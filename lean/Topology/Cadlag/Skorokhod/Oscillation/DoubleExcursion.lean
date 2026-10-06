/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Oscillation.Partition.Measurability

/-!
# Billingsley's double-excursion modulus

This module defines the pathwise double-excursion and endpoint controls used
in the Skorokhod compactness criterion. It proves that an oscillation
partition implies these controls; the converse construction lives in
`Topology.Cadlag.Skorokhod.Oscillation.DoubleExcursion.Converse`.
-/

@[expose] public section

open Set
open Filter
open scoped Topology

namespace Skorokhod

/-- Every pair of excursions on the two sides of any split in an interval
shorter than `delta` has one side of size at most `epsilon`. The two
excursions are measured by arbitrary pairs of points in their respective
closed subintervals. -/
def HasDoubleExcursionBound {E : Type*} [PseudoMetricSpace E]
    (path : CadlagPath unitInterval E) (delta epsilon : ℝ) : Prop :=
  ∀ s t u : unitInterval, s < t → t < u → u ≠ ⊤ → dist s u < delta →
    ∀ x y z w : unitInterval,
      s ≤ x → x ≤ y → y ≤ t →
      t ≤ z → z ≤ w → w ≤ u →
      min (dist (path x) (path y)) (dist (path z) (path w)) ≤ epsilon

/-- Uniform control of the path oscillation near both endpoints. The terminal
value is excluded from the right endpoint control because the partition
criterion treats it as a separate coordinate. -/
def HasEndpointOscillationBound {E : Type*} [PseudoMetricSpace E]
    (path : CadlagPath unitInterval E) (delta epsilon : ℝ) : Prop :=
  (∀ s t : unitInterval, (s : ℝ) < delta → (t : ℝ) < delta →
      dist (path s) (path t) ≤ epsilon) ∧
  (∀ s t : unitInterval, s ≠ ⊤ → t ≠ ⊤ →
      1 - delta < (s : ℝ) → 1 - delta < (t : ℝ) →
      dist (path s) (path t) ≤ epsilon)

private theorem OscillationPartition.mesh_le_coe_of_positive_index
    (partition : OscillationPartition) (i : Fin partition.size)
    (hi : 0 < i.val) :
    partition.mesh ≤ (partition.points i.castSucc : ℝ) := by
  let firstCell : Fin partition.size := ⟨0, partition.size_pos⟩
  have hfirstLe : firstCell.succ ≤ i.castSucc := by
    apply Fin.le_iff_val_le_val.mpr
    simp [firstCell]
    exact hi
  have hpoints := partition.strictMono_points.monotone hfirstLe
  have hfirstPoint : partition.points firstCell.castSucc = ⊥ := by
    simpa [firstCell] using partition.first
  have hdist : dist (⊥ : unitInterval) (partition.points firstCell.succ) =
      (partition.points firstCell.succ : ℝ) := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have hnonneg : 0 ≤ (partition.points firstCell.succ : ℝ) :=
      (partition.points firstCell.succ).property.1
    simp [abs_of_nonpos, hnonneg]
  have hgap := partition.gap_lower firstCell
  rw [hfirstPoint, hdist] at hgap
  exact hgap.trans (by exact_mod_cast hpoints)

private theorem OscillationPartition.coe_le_one_sub_mesh
    (partition : OscillationPartition) (i : Fin partition.size) :
    (partition.points i.castSucc : ℝ) ≤ 1 - partition.mesh := by
  let lastCell : Fin partition.size :=
    ⟨partition.size - 1, Nat.sub_lt partition.size_pos (by decide)⟩
  have hindexLe : i.castSucc ≤ lastCell.castSucc := by
    apply Fin.le_iff_val_le_val.mpr
    change i.val ≤ partition.size - 1
    omega
  have hpointsLe := partition.strictMono_points.monotone hindexLe
  have hlastSucc : lastCell.succ = Fin.last partition.size := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_last]
    dsimp [lastCell]
    have hsize : 1 ≤ partition.size := Nat.succ_le_iff.mpr partition.size_pos
    omega
  have hlastPoint : partition.points lastCell.succ = ⊤ := by
    rw [hlastSucc]
    simpa [Fin.last] using partition.last
  have hdist : dist (partition.points lastCell.castSucc) (⊤ : unitInterval) =
      1 - (partition.points lastCell.castSucc : ℝ) := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have hleOne : (partition.points lastCell.castSucc : ℝ) ≤ 1 :=
      (partition.points lastCell.castSucc).property.2
    change |(partition.points lastCell.castSucc : ℝ) - 1| = _
    rw [abs_of_nonpos (by linarith)]
    ring
  have hgap := partition.gap_lower lastCell
  rw [hlastPoint, hdist] at hgap
  have hle : (partition.points i.castSucc : ℝ) ≤
      (partition.points lastCell.castSucc : ℝ) := by exact_mod_cast hpointsLe
  linarith

private theorem unitInterval_ne_top_of_coe_lt_one {t : unitInterval}
    (ht : (t : ℝ) < 1) : t ≠ ⊤ := by
  intro heq
  have hval : (t : ℝ) = 1 := by simp [heq]
  linarith

private theorem OscillationPartition.mesh_le_one
    (partition : OscillationPartition) : partition.mesh ≤ 1 := by
  have hsize : 1 ≤ (partition.size : ℝ) := by
    exact_mod_cast partition.size_pos
  have hmul := partition.size_mul_mesh_le_one
  have hmesh := partition.mesh_pos
  nlinarith

private theorem OscillationPartition.leftEndpoint_dist_le
    {E : Type*} [PseudoMetricSpace E]
    (partition : OscillationPartition) (path : CadlagPath unitInterval E)
    {delta epsilon : ℝ} (hmesh : delta ≤ partition.mesh)
    (hosc : OscillationBoundedOnPartition partition path epsilon)
    {s t : unitInterval} (hst : s ≤ t)
    (hsδ : (s : ℝ) < delta) (htδ : (t : ℝ) < delta) :
    dist (path s) (path t) ≤ epsilon := by
  have hδOne : delta ≤ 1 := hmesh.trans partition.mesh_le_one
  have hsTop : s ≠ ⊤ :=
    unitInterval_ne_top_of_coe_lt_one (lt_of_lt_of_le hsδ hδOne)
  have htTop : t ≠ ⊤ :=
    unitInterval_ne_top_of_coe_lt_one (lt_of_lt_of_le htδ hδOne)
  by_cases hindex : partition.index s = partition.index t
  · exact hosc s t hsTop htTop hindex
  · have hidx : partition.index s < partition.index t :=
      lt_of_le_of_ne (partition.index_monotone hst) hindex
    let j := partition.index t
    have hjpos : 0 < j.val := by
      dsimp [j]
      have hval := Fin.lt_def.mp hidx
      omega
    let q := partition.points j.castSucc
    have hstart : partition.index q = partition.index t := by
      dsimp [q, j]
      exact partition.index_start (partition.index t)
    have hsltq : s < q := by
      by_contra hnot
      have hqs : q ≤ s := le_of_not_gt hnot
      have hidxqs := partition.index_monotone hqs
      rw [hstart] at hidxqs
      exact (not_lt_of_ge hidxqs) hidx
    have hqt : q ≤ t := partition.index_lower t
    have hmeshQ := partition.mesh_le_coe_of_positive_index j hjpos
    have hqδ : (q : ℝ) < delta := lt_of_le_of_lt (by exact_mod_cast hqt) htδ
    have hδq : delta ≤ (q : ℝ) := hmesh.trans hmeshQ
    linarith

private theorem OscillationPartition.rightEndpoint_dist_le
    {E : Type*} [PseudoMetricSpace E]
    (partition : OscillationPartition) (path : CadlagPath unitInterval E)
    {delta epsilon : ℝ} (hmesh : delta ≤ partition.mesh)
    (hosc : OscillationBoundedOnPartition partition path epsilon)
    {s t : unitInterval} (hst : s ≤ t) (hsTop : s ≠ ⊤) (htTop : t ≠ ⊤)
    (hsδ : 1 - delta < (s : ℝ)) (_htδ : 1 - delta < (t : ℝ)) :
    dist (path s) (path t) ≤ epsilon := by
  by_cases hindex : partition.index s = partition.index t
  · exact hosc s t hsTop htTop hindex
  · have hidx : partition.index s < partition.index t :=
      lt_of_le_of_ne (partition.index_monotone hst) hindex
    let j := partition.index t
    let q := partition.points j.castSucc
    have hstart : partition.index q = partition.index t := by
      dsimp [q, j]
      exact partition.index_start (partition.index t)
    have hsltq : s < q := by
      by_contra hnot
      have hqs : q ≤ s := le_of_not_gt hnot
      have hidxqs := partition.index_monotone hqs
      rw [hstart] at hidxqs
      exact (not_lt_of_ge hidxqs) hidx
    have hqt : q ≤ t := partition.index_lower t
    have hqUpper := partition.coe_le_one_sub_mesh j
    have hsUpper : (s : ℝ) ≤ 1 - partition.mesh :=
      le_trans (by exact_mod_cast hsltq.le) hqUpper
    have hmeshDelta : delta ≤ partition.mesh := hmesh
    have hsLower : 1 - delta < (s : ℝ) := hsδ
    have hcontr : (s : ℝ) ≤ 1 - delta := by linarith
    exact (not_lt_of_ge hcontr hsLower).elim

/-- A partition with cell oscillation at most `epsilon` bounds the
double-excursion modulus at every time scale no larger than its minimum gap.
The terminal time is excluded, consistently with the separate terminal
coordinate in `OscillationBoundedOnPartition`. -/
theorem OscillationBoundedOnPartition.hasDoubleExcursionBound
    {E : Type*} [PseudoMetricSpace E]
    (partition : OscillationPartition) (path : CadlagPath unitInterval E)
    {delta epsilon : ℝ} (hmesh : delta ≤ partition.mesh)
    (hosc : OscillationBoundedOnPartition partition path epsilon) :
    HasDoubleExcursionBound path delta epsilon := by
  intro s t u hst htu huTop hdist x y z w hsx hxyTime hyt htz hzwTime hwu
  have hu_lt_top : u < ⊤ := lt_top_iff_ne_top.mpr huTop
  have hx_lt_top : x < ⊤ :=
    lt_of_le_of_lt (hxyTime.trans hyt) (htu.trans hu_lt_top)
  have hy_lt_top : y < ⊤ := lt_of_le_of_lt hyt (htu.trans hu_lt_top)
  have hz_lt_top : z < ⊤ := lt_of_le_of_lt (hzwTime.trans hwu) hu_lt_top
  have hw_lt_top : w < ⊤ := lt_of_le_of_lt hwu hu_lt_top
  by_cases hxy : partition.index x = partition.index y
  · exact (min_le_left _ _).trans
      (hosc x y (ne_of_lt hx_lt_top) (ne_of_lt hy_lt_top) hxy)
  · by_cases hzw : partition.index z = partition.index w
    · exact (min_le_right _ _).trans
        (hosc z w (ne_of_lt hz_lt_top) (ne_of_lt hw_lt_top) hzw)
    · have hixy : partition.index x ≤ partition.index y :=
        partition.index_monotone hxyTime
      have hixy' : partition.index x < partition.index y :=
        lt_of_le_of_ne hixy hxy
      have hizw : partition.index z ≤ partition.index w :=
        partition.index_monotone hzwTime
      have hizw' : partition.index z < partition.index w :=
        lt_of_le_of_ne hizw hzw
      have hiyz : partition.index y ≤ partition.index z :=
        partition.index_monotone (hyt.trans htz)
      let i := partition.index y
      let j := partition.index w
      let q := partition.points i.castSucc
      let r := partition.points j.castSucc
      have hqle : q ≤ y := by
        exact partition.index_lower y
      have hrle : r ≤ w := by
        exact partition.index_lower w
      have hxq : x < q := by
        by_contra hnot
        have hqx : q ≤ x := le_of_not_gt hnot
        have hindex := partition.index_monotone hqx
        have hstart : partition.index q = partition.index y := by
          dsimp [q, i]
          exact partition.index_start (partition.index y)
        rw [hstart] at hindex
        exact (not_lt_of_ge hindex) hixy'
      have hzr : z < r := by
        by_contra hnot
        have hrz : r ≤ z := le_of_not_gt hnot
        have hindex := partition.index_monotone hrz
        have hstart : partition.index r = partition.index w := by
          dsimp [r, j]
          exact partition.index_start (partition.index w)
        rw [hstart] at hindex
        exact (not_lt_of_ge hindex) hizw'
      have hij : i < j := by
        dsimp [i, j]
        exact lt_of_le_of_lt hiyz hizw'
      have hqr : q < r := by
        dsimp [q, r, i, j]
        apply partition.strictMono_points
        apply Fin.lt_def.mpr
        simpa using (Fin.lt_def.mp hij)
      have hsuccLe : i.succ ≤ j.castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        rw [Fin.val_succ, Fin.val_castSucc]
        exact Nat.succ_le_of_lt (Fin.lt_def.mp hij)
      have hqNext : q ≤ partition.points i.succ := by
        dsimp [q]
        exact le_of_lt (partition.strictMono_points i.castSucc_lt_succ)
      have hnextR : partition.points i.succ ≤ r := by
        dsimp [r, j]
        exact partition.strictMono_points.monotone hsuccLe
      have hmeshQr : partition.mesh ≤ dist q r := by
        calc
          partition.mesh ≤ dist (partition.points i.castSucc)
              (partition.points i.succ) := partition.gap_lower i
          _ = dist q (partition.points i.succ) := by rfl
          _ ≤ dist q r := unitInterval_dist_le_of_subintervals le_rfl hqNext hnextR
      have hsQ : s ≤ q := le_trans hsx hxq.le
      have hrU : r ≤ u := le_trans hrle hwu
      have hqrSu : dist q r ≤ dist s u :=
        unitInterval_dist_le_of_subintervals hsQ (le_of_lt hqr) hrU
      have hmeshLt : partition.mesh < delta :=
        lt_of_le_of_lt (hmeshQr.trans hqrSu) hdist
      exact (not_lt_of_ge hmesh hmeshLt).elim

/-- Cellwise oscillation control and a common cell-gap lower bound imply the
corresponding oscillation controls at both endpoints. -/
theorem OscillationBoundedOnPartition.hasEndpointOscillationBound
    {E : Type*} [PseudoMetricSpace E]
    (partition : OscillationPartition) (path : CadlagPath unitInterval E)
    {delta epsilon : ℝ} (hmesh : delta ≤ partition.mesh)
    (hosc : OscillationBoundedOnPartition partition path epsilon) :
    HasEndpointOscillationBound path delta epsilon := by
  constructor
  · intro s t hsδ htδ
    rcases le_total s t with hst | hts
    · exact partition.leftEndpoint_dist_le path hmesh hosc hst hsδ htδ
    · simpa [dist_comm] using
        partition.leftEndpoint_dist_le path hmesh hosc hts htδ hsδ
  · intro s t hsTop htTop hsδ htδ
    rcases le_total s t with hst | hts
    · exact partition.rightEndpoint_dist_le path hmesh hosc hst hsTop htTop hsδ htδ
    · simpa [dist_comm] using
        partition.rightEndpoint_dist_le path hmesh hosc hts htTop hsTop htδ hsδ

/-- A uniform oscillation-partition criterion supplies uniform double-
excursion and endpoint controls with the same mesh and oscillation scales.
This is the necessary direction; `w''` alone does not encode the endpoint
controls needed for the converse. -/
theorem forall_mem_admitsOscillationPartition_hasBillingsleyControls
    {E : Type*} [MetricSpace E] {K : Set (CadlagPath unitInterval E)}
    {minimumGap maximumOscillation : ℝ}
    (hpart : ∀ path ∈ K,
      path ∈ admitsOscillationPartition minimumGap maximumOscillation) :
    ∀ path ∈ K,
      HasDoubleExcursionBound path minimumGap maximumOscillation ∧
      HasEndpointOscillationBound path minimumGap maximumOscillation := by
  intro path hpath
  obtain ⟨partition, hgap, bound, hbound, hosc⟩ := hpart path hpath
  have hosc' : OscillationBoundedOnPartition partition path maximumOscillation := by
    intro s t hs ht hindex
    exact (hosc s t hs ht hindex).trans (le_of_lt hbound)
  have hmesh : minimumGap ≤ partition.mesh := le_of_lt hgap
  exact ⟨OscillationBoundedOnPartition.hasDoubleExcursionBound
      partition path hmesh hosc',
    OscillationBoundedOnPartition.hasEndpointOscillationBound
      partition path hmesh hosc'⟩


end Skorokhod

end

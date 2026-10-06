/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Oscillation.Partition.Finite
public import Topology.Cadlag.Skorokhod.Oscillation.Partition.Measurability
public import Topology.Cadlag.Oscillation
public import Mathlib.Data.Finset.Sort

/-!
# Finite small-oscillation partitions for càdlàg paths

Every càdlàg path on the compact unit interval admits a finite partition on
whose half-open cells the oscillation is arbitrarily small.  The proof uses
the one-sided local oscillation bounds and refines a finite interval cover at
the finitely many selected centers.
-/

@[expose] public section

open Set
open scoped Topology

namespace Skorokhod

private noncomputable def chosenLeftOscillationRadius
    {E : Type*} [PseudoMetricSpace E] {f : unitInterval → E}
    (hf : IsCadlag f) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (t : unitInterval) : ℝ :=
  Classical.choose (hf.exists_left_oscillation_radius t hepsilon)

private theorem chosenLeftOscillationRadius_pos
    {E : Type*} [PseudoMetricSpace E] {f : unitInterval → E}
    (hf : IsCadlag f) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (t : unitInterval) :
    0 < chosenLeftOscillationRadius hf epsilon hepsilon t := by
  exact (Classical.choose_spec
    (hf.exists_left_oscillation_radius t hepsilon)).1

private theorem chosenLeftOscillationRadius_spec
    {E : Type*} [PseudoMetricSpace E] {f : unitInterval → E}
    (hf : IsCadlag f) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (t s u : unitInterval)
    (hst : s < t) (hut : u < t)
    (hds : dist s t < chosenLeftOscillationRadius hf epsilon hepsilon t)
    (hdu : dist u t < chosenLeftOscillationRadius hf epsilon hepsilon t) :
    dist (f s) (f u) ≤ epsilon := by
  have h := (Classical.choose_spec
    (hf.exists_left_oscillation_radius t hepsilon)).2
    s u hst hut
  exact h hds hdu

private noncomputable def chosenRightOscillationRadius
    {E : Type*} [PseudoMetricSpace E] {f : unitInterval → E}
    (hf : IsCadlag f) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (t : unitInterval) : ℝ :=
  Classical.choose (hf.exists_right_oscillation_radius t hepsilon)

private theorem chosenRightOscillationRadius_pos
    {E : Type*} [PseudoMetricSpace E] {f : unitInterval → E}
    (hf : IsCadlag f) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (t : unitInterval) :
    0 < chosenRightOscillationRadius hf epsilon hepsilon t := by
  exact (Classical.choose_spec
    (hf.exists_right_oscillation_radius t hepsilon)).1

private theorem chosenRightOscillationRadius_spec
    {E : Type*} [PseudoMetricSpace E] {f : unitInterval → E}
    (hf : IsCadlag f) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (t s u : unitInterval)
    (hst : t ≤ s) (hut : t ≤ u)
    (hds : dist s t < chosenRightOscillationRadius hf epsilon hepsilon t)
    (hdu : dist u t < chosenRightOscillationRadius hf epsilon hepsilon t) :
    dist (f s) (f u) ≤ epsilon := by
  have h := (Classical.choose_spec
    (hf.exists_right_oscillation_radius t hepsilon)).2
    s u hst hut
  exact h hds hdu

private noncomputable def localOscillationRadius
    {E : Type*} [PseudoMetricSpace E] {f : unitInterval → E}
    (hf : IsCadlag f) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (t : unitInterval) : ℝ :=
  min (chosenLeftOscillationRadius hf epsilon hepsilon t)
    (chosenRightOscillationRadius hf epsilon hepsilon t)

private theorem localOscillationRadius_pos
    {E : Type*} [PseudoMetricSpace E] {f : unitInterval → E}
    (hf : IsCadlag f) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (t : unitInterval) :
    0 < localOscillationRadius hf epsilon hepsilon t := by
  exact lt_min (chosenLeftOscillationRadius_pos hf hepsilon t)
    (chosenRightOscillationRadius_pos hf hepsilon t)

/-- A càdlàg path on the unit interval has a finite partition with
arbitrarily small oscillation on each half-open cell. -/
theorem IsCadlag.exists_oscillation_partition
    {E : Type*} [PseudoMetricSpace E] {f : unitInterval → E} (hf : IsCadlag f)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ partition : OscillationPartition, ∃ bound : ℝ,
      bound < epsilon ∧
        OscillationBoundedOnPartition partition ⟨f, hf⟩ bound := by
  classical
  let localEpsilon := epsilon / 2
  have hlocalEpsilon : 0 < localEpsilon := by dsimp [localEpsilon]; positivity
  let radius := localOscillationRadius hf localEpsilon hlocalEpsilon
  let neighborhood : unitInterval → Set unitInterval := fun c =>
    Metric.ball c (radius c)
  have hradius (c : unitInterval) : 0 < radius c :=
    localOscillationRadius_pos hf hlocalEpsilon c
  have hneighborhoodOpen (c : unitInterval) : IsOpen (neighborhood c) :=
    Metric.isOpen_ball
  have hneighborhoodCover : (Set.univ : Set unitInterval) ⊆
      ⋃ c, neighborhood c := by
    intro c _
    exact Set.mem_iUnion.mpr ⟨c, Metric.mem_ball_self (hradius c)⟩
  obtain ⟨centers, hcenters⟩ :=
    isCompact_univ.elim_finite_subcover neighborhood hneighborhoodOpen
      hneighborhoodCover
  let finiteNeighborhood : centers → Set unitInterval :=
    fun c => neighborhood c.1
  have hfiniteCover : (Set.univ : Set unitInterval) ⊆
      ⋃ c : centers, finiteNeighborhood c := by
    intro x _
    obtain ⟨c, hc, hx⟩ := Set.mem_iUnion₂.mp (hcenters (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨c, hc⟩, hx⟩
  obtain ⟨gridTime, hgridStart, hgridMono, hgridEnd⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun (c : centers) => hneighborhoodOpen c.1) hfiniteCover
  obtain ⟨⟨gridEndIndex, hgridTerminal⟩, hgridCells⟩ := hgridEnd
  let gridPoints : Finset unitInterval :=
    Finset.image gridTime (Finset.range (gridEndIndex + 1))
  let centerPoints : Finset unitInterval :=
    Finset.univ.image (fun c : centers => (c : unitInterval))
  let pointsSet : Finset unitInterval := gridPoints ∪ centerPoints
  have hgridZero : (⊥ : unitInterval) ∈ gridPoints := by
    apply Finset.mem_image.mpr
    refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    exact hgridStart.trans bot_eq_zero.symm
  have hgridTop : (⊤ : unitInterval) ∈ gridPoints := by
    apply Finset.mem_image.mpr
    refine ⟨gridEndIndex, Finset.mem_range.mpr (by omega), ?_⟩
    have h := hgridTerminal gridEndIndex le_rfl
    have hone : (1 : unitInterval) = ⊤ := Subtype.ext rfl
    simpa [hone] using h
  have hbottomPoints : (⊥ : unitInterval) ∈ pointsSet :=
    Finset.mem_union.mpr (Or.inl hgridZero)
  have htopPoints : (⊤ : unitInterval) ∈ pointsSet :=
    Finset.mem_union.mpr (Or.inl hgridTop)
  have hendpoints : ({(⊥ : unitInterval), ⊤} : Finset unitInterval) ⊆
      pointsSet := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hbottomPoints
    · exact htopPoints
  have hcardLower : 2 ≤ pointsSet.card := by
    have hpair : ({(⊥ : unitInterval), ⊤} : Finset unitInterval).card = 2 :=
      Finset.card_pair bot_ne_top
    exact hpair ▸ Finset.card_le_card hendpoints
  let size := pointsSet.card - 1
  have hsizeCard : size + 1 = pointsSet.card :=
    Nat.sub_add_cancel (by omega : 1 ≤ pointsSet.card)
  let orderedPoints : Fin pointsSet.card → unitInterval :=
    pointsSet.orderEmbOfFin rfl
  let points : Fin (size + 1) → unitInterval := fun i =>
    orderedPoints (Fin.cast hsizeCard i)
  have hpointsStrict : StrictMono points := by
    apply StrictMono.comp (pointsSet.orderEmbOfFin rfl).strictMono
    intro i j hij
    apply Fin.lt_def.mpr
    simpa [Fin.val_cast] using (Fin.lt_def.mp hij)
  have hpointsBottom : points ⟨0, by omega⟩ = ⊥ := by
    have hmem : (⊥ : unitInterval) ∈ (pointsSet : Set unitInterval) := hbottomPoints
    rw [← pointsSet.range_orderEmbOfFin rfl] at hmem
    obtain ⟨i, hi⟩ := hmem
    let zeroIndex : Fin pointsSet.card := ⟨0, by omega⟩
    have hzero : zeroIndex ≤ i := Fin.le_iff_val_le_val.mpr (by simp [zeroIndex])
    have hle := (pointsSet.orderEmbOfFin rfl).monotone hzero
    have hbottom : (pointsSet.orderEmbOfFin rfl) i = ⊥ := hi
    have hraw : (pointsSet.orderEmbOfFin rfl) zeroIndex ≤ ⊥ := by
      simpa [hbottom] using hle
    change orderedPoints (Fin.cast hsizeCard ⟨0, by omega⟩) = ⊥
    have hcast : Fin.cast hsizeCard (⟨0, by omega⟩ : Fin (size + 1)) = zeroIndex := by
      apply Fin.ext
      simp [zeroIndex, Fin.val_cast]
    rw [hcast]
    exact le_antisymm hraw bot_le
  have hpointsTop : points ⟨size, by omega⟩ = ⊤ := by
    have hmem : (⊤ : unitInterval) ∈ (pointsSet : Set unitInterval) := htopPoints
    rw [← pointsSet.range_orderEmbOfFin rfl] at hmem
    obtain ⟨i, hi⟩ := hmem
    let hlast : Fin pointsSet.card := ⟨size, by omega⟩
    have hiSize : i.val < size + 1 := by simp [hsizeCard]
    have hlastVal : hlast.val = size := rfl
    have hle : i ≤ hlast := Fin.le_iff_val_le_val.mpr (by
      rw [hlastVal]
      exact Nat.le_of_lt_succ hiSize)
    have hmono := (pointsSet.orderEmbOfFin rfl).monotone hle
    have htop : (pointsSet.orderEmbOfFin rfl) i = ⊤ := hi
    have hraw : ⊤ ≤ (pointsSet.orderEmbOfFin rfl) hlast := by
      simpa [htop] using hmono
    have hupper : (pointsSet.orderEmbOfFin rfl) hlast ≤ ⊤ := le_top
    have hlastEq : (pointsSet.orderEmbOfFin rfl) hlast = ⊤ :=
      le_antisymm hupper hraw
    change orderedPoints (Fin.cast hsizeCard ⟨size, by omega⟩) = ⊤
    have hlastCast :
      Fin.cast hsizeCard (⟨size, by omega⟩ : Fin (size + 1)) = hlast := by
      apply Fin.ext
      rw [Fin.val_cast, hlastVal]
    rw [hlastCast]
    exact hlastEq
  let partition := OscillationPartition.ofFinitePoints
    (by omega : 0 < size) points hpointsBottom hpointsTop hpointsStrict
  refine ⟨partition, localEpsilon, ?_, ?_⟩
  · dsimp [localEpsilon]
    linarith
  · intro s t hsTop htTop hsame
    let i : Fin size := partition.index s
    have hindexT : partition.index t = i := hsame.symm
    have hleftS : partition.points i.castSucc ≤ s := by
      change partition.points (partition.index s).castSucc ≤ s
      exact partition.index_lower s
    have hleftT : partition.points i.castSucc ≤ t := by
      change partition.points (partition.index s).castSucc ≤ t
      rw [hsame]
      exact partition.index_lower t
    have hupperAt (x : unitInterval) (hxTop : x ≠ ⊤)
        (hxi : partition.index x = i) : x < partition.points i.succ := by
      rcases partition.index_upper x with h | hlast
      · exact hxi ▸ h
      · have hindexLast : i.succ = Fin.last partition.size := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_last]
          omega
        have hlastFin : (Fin.last partition.size : Fin (partition.size + 1)) =
            ⟨partition.size, by omega⟩ := by
          apply Fin.ext
          rfl
        have hpointLast : partition.points i.succ = ⊤ := by
          rw [hindexLast, hlastFin, partition.last]
        rw [hpointLast]
        exact lt_top_iff_ne_top.mpr hxTop
    have hrightS : s < partition.points i.succ := hupperAt s hsTop rfl
    have hrightT : t < partition.points i.succ := hupperAt t htTop hindexT
    have hleftTop : partition.points i.castSucc < ⊤ := by
      rw [← hpointsTop]
      have hiLast : i.castSucc < Fin.last size := by
        apply Fin.lt_def.mpr
        simp only [Fin.val_castSucc, Fin.val_last]
        exact i.isLt
      exact hpointsStrict hiLast
    have hnoMiddle (z : unitInterval) (hz : z ∈ pointsSet)
        (hlz : points i.castSucc < z) (hzr : z < points i.succ) : False := by
      have hzRange : z ∈ Set.range (pointsSet.orderEmbOfFin rfl) := by
        rw [pointsSet.range_orderEmbOfFin]
        exact hz
      obtain ⟨j, hj⟩ := Set.mem_range.mp hzRange
      have hleftPoint :
          (pointsSet.orderEmbOfFin rfl) (Fin.cast hsizeCard i.castSucc) =
            partition.points i.castSucc := by
        rfl
      have hrightPoint :
          (pointsSet.orderEmbOfFin rfl) (Fin.cast hsizeCard i.succ) =
            partition.points i.succ := by
        rfl
      have hlRaw : (pointsSet.orderEmbOfFin rfl)
          (Fin.cast hsizeCard i.castSucc) <
            (pointsSet.orderEmbOfFin rfl) j := by
        calc
          _ = partition.points i.castSucc := hleftPoint
          _ < z := hlz
          _ = _ := hj.symm
      have hrRaw : (pointsSet.orderEmbOfFin rfl) j <
          (pointsSet.orderEmbOfFin rfl) (Fin.cast hsizeCard i.succ) := by
        calc
          _ = z := hj
          _ < partition.points i.succ := hzr
          _ = _ := hrightPoint.symm
      have hlFin := (pointsSet.orderEmbOfFin rfl).lt_iff_lt.mp hlRaw
      have hrFin := (pointsSet.orderEmbOfFin rfl).lt_iff_lt.mp hrRaw
      have hlVal : i.val < j.val := by
        have h := Fin.lt_def.mp hlFin
        have hcastVal : (Fin.cast hsizeCard i.castSucc).val = i.val := by
          simp [Fin.val_cast]
        rw [hcastVal] at h
        exact h
      have hrVal : j.val < i.val + 1 := by
        have h := Fin.lt_def.mp hrFin
        have hcastVal : (Fin.cast hsizeCard i.succ).val = i.val + 1 := by
          simp [Fin.val_cast, Fin.val_succ]
        rw [hcastVal] at h
        exact h
      omega
    let candidates : Finset ℕ :=
      (Finset.range (gridEndIndex + 1)).filter
        (fun k => gridTime k ≤ partition.points i.castSucc)
    have hcandidatesNonempty : candidates.Nonempty := by
      refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
      rw [hgridStart]
      exact bot_le
    let k := candidates.max' hcandidatesNonempty
    have hkmem : k ∈ candidates := by
      change candidates.max' hcandidatesNonempty ∈ candidates
      exact Finset.max'_mem _ _
    have hkRange : k < gridEndIndex + 1 :=
      (Finset.mem_filter.mp hkmem).1 |> Finset.mem_range.mp
    have hkLeft : gridTime k ≤ partition.points i.castSucc :=
      (Finset.mem_filter.mp hkmem).2
    have hkLeEnd : k ≤ gridEndIndex := by omega
    have hkLtEnd : k < gridEndIndex := by
      by_contra hnot
      have hkEq : k = gridEndIndex := by omega
      have hterminal : gridTime k = ⊤ := by
        rw [hkEq]
        have h := hgridTerminal gridEndIndex le_rfl
        have hone : (1 : unitInterval) = ⊤ := Subtype.ext rfl
        simpa [hone] using h
      have hfalse : ⊤ ≤ partition.points i.castSucc := by
        rw [← hterminal]
        exact hkLeft
      exact (not_le_of_gt hleftTop) hfalse
    have hsuccNot : k + 1 ∉ candidates := by
      intro hmem
      have hle := Finset.le_max' candidates (k + 1) hmem
      omega
    have hkRight : partition.points i.castSucc < gridTime (k + 1) := by
      by_contra hnot
      have hle : gridTime (k + 1) ≤ partition.points i.castSucc := le_of_not_gt hnot
      have hmem : k + 1 ∈ candidates := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_range.mpr (by omega), hle⟩
      exact hsuccNot hmem
    have hgridMem (m : ℕ) (hm : m ≤ gridEndIndex) :
        gridTime m ∈ pointsSet := by
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      exact ⟨m, Finset.mem_range.mpr (by omega), rfl⟩
    have hnextMem : gridTime (k + 1) ∈ pointsSet := hgridMem (k + 1) (by omega)
    have hrightGrid : partition.points i.succ ≤ gridTime (k + 1) := by
      by_contra hnot
      exact hnoMiddle (gridTime (k + 1)) hnextMem hkRight (lt_of_not_ge hnot)
    obtain ⟨center, hcenterCell⟩ := hgridCells k
    have hsGrid : s ∈ Set.Icc (gridTime k) (gridTime (k + 1)) := by
      exact ⟨hkLeft.trans hleftS, (hrightS.trans_le hrightGrid).le⟩
    have htGrid : t ∈ Set.Icc (gridTime k) (gridTime (k + 1)) := by
      exact ⟨hkLeft.trans hleftT, (hrightT.trans_le hrightGrid).le⟩
    have hsBall : s ∈ neighborhood center.1 := hcenterCell hsGrid
    have htBall : t ∈ neighborhood center.1 := hcenterCell htGrid
    have hcenterMem : (center : unitInterval) ∈ pointsSet := by
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      exact ⟨center, Finset.mem_univ _, rfl⟩
    by_cases hcenterLeft : (center : unitInterval) ≤ partition.points i.castSucc
    · have hds : dist s center <
          chosenRightOscillationRadius hf localEpsilon hlocalEpsilon center := by
        have hball := Metric.mem_ball.mp hsBall
        exact lt_of_lt_of_le hball (by simp [radius, localOscillationRadius])
      have hdt : dist t center <
          chosenRightOscillationRadius hf localEpsilon hlocalEpsilon center := by
        have hball := Metric.mem_ball.mp htBall
        exact lt_of_lt_of_le hball (by simp [radius, localOscillationRadius])
      exact chosenRightOscillationRadius_spec hf hlocalEpsilon center s t
        (hcenterLeft.trans hleftS) (hcenterLeft.trans hleftT) hds hdt
    · have hleftCenter : partition.points i.castSucc < center := lt_of_not_ge hcenterLeft
      have hcenterRight : partition.points i.succ ≤ center := by
        by_contra hnot
        exact hnoMiddle center hcenterMem hleftCenter (lt_of_not_ge hnot)
      have hsCenter : s < center := hrightS.trans_le hcenterRight
      have htCenter : t < center := hrightT.trans_le hcenterRight
      have hds : dist s center <
          chosenLeftOscillationRadius hf localEpsilon hlocalEpsilon center := by
        have hball := Metric.mem_ball.mp hsBall
        exact lt_of_lt_of_le hball (by simp [radius, localOscillationRadius])
      have hdt : dist t center <
          chosenLeftOscillationRadius hf localEpsilon hlocalEpsilon center := by
        have hball := Metric.mem_ball.mp htBall
        exact lt_of_lt_of_le hball (by simp [radius, localOscillationRadius])
      exact chosenLeftOscillationRadius_spec hf hlocalEpsilon center s t
        hsCenter htCenter hds hdt

/-- Each càdlàg path admits a positive cell-gap partition with any prescribed
positive oscillation tolerance. -/
theorem CadlagPath.exists_admits_oscillation_partition
    (path : CadlagPath unitInterval ℝ) {maximumOscillation : ℝ}
    (hmaximumOscillation : 0 < maximumOscillation) :
    ∃ minimumGap > 0,
      path ∈ admitsOscillationPartition minimumGap maximumOscillation := by
  obtain ⟨partition, bound, hbound, hosc⟩ :=
    IsCadlag.exists_oscillation_partition path.isCadlag_toFun hmaximumOscillation
  refine ⟨partition.mesh / 2, by linarith [partition.mesh_pos], ?_⟩
  exact ⟨partition, by linarith [partition.mesh_pos], bound, hbound, hosc⟩

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Oscillation.DoubleExcursion
import Topology.Cadlag.Skorokhod.Oscillation.DoubleExcursion.JumpControl
import Topology.Cadlag.Skorokhod.Oscillation.Partition.Finite
import Topology.Cadlag.Jump
import Order.Interval.UniformGrid

/-!
# Converse to the double-excursion criterion

A càdlàg path satisfying uniform double-excursion and endpoint controls has
an oscillation partition with a uniform mesh lower bound. The proof isolates
large jumps and filters a uniform grid around them.
-/

@[expose] public section

open Set
open Filter
open scoped Topology

namespace Skorokhod

private theorem unitInterval_dist_eq_coe_sub {a b : unitInterval} (hab : a ≤ b) :
    dist a b = (b : ℝ) - (a : ℝ) := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab')]
  ring

private theorem unitInterval_dist_bot_eq (t : unitInterval) :
    dist (⊥ : unitInterval) t = (t : ℝ) := by
  rw [unitInterval_dist_eq_coe_sub bot_le]
  simp

private theorem unitInterval_dist_top_eq (t : unitInterval) :
    dist (⊤ : unitInterval) t = 1 - (t : ℝ) := by
  rw [dist_comm, unitInterval_dist_eq_coe_sub (le_top : t ≤ ⊤)]
  simp

private noncomputable def unitGridPoint (blocks : ℕ) (hblocks : 0 < blocks)
    (i : Fin (blocks + 1)) : unitInterval := by
  let grid : UniformGrid ℝ := UniformGrid.unit (K := ℝ) blocks hblocks
  exact ⟨grid.point i, by simpa [grid] using UniformGrid.point_mem_Icc grid i⟩

private theorem unitGridPoint_coe (blocks : ℕ) (hblocks : 0 < blocks)
    (i : Fin (blocks + 1)) :
    (unitGridPoint blocks hblocks i : ℝ) = (i : ℝ) / blocks := by
  change (UniformGrid.unit (K := ℝ) blocks hblocks).point i = (i : ℝ) / blocks
  exact UniformGrid.unit_point (K := ℝ) blocks hblocks i

private theorem unitGridPoint_strictMono (blocks : ℕ) (hblocks : 0 < blocks) :
    StrictMono (unitGridPoint blocks hblocks) := by
  intro i j hij
  apply Subtype.coe_lt_coe.mpr
  let grid : UniformGrid ℝ := UniformGrid.unit (K := ℝ) blocks hblocks
  change grid.point i < grid.point j
  exact UniformGrid.strictMono_point (grid := grid) (by norm_num [grid]) hij

private theorem unitGridPoint_step_distance (blocks : ℕ) (hblocks : 0 < blocks)
    (i : Fin blocks) :
    dist (unitGridPoint blocks hblocks i.castSucc)
      (unitGridPoint blocks hblocks i.succ) = 1 / (blocks : ℝ) := by
  rw [Subtype.dist_eq, Real.dist_eq]
  have hmono : (unitGridPoint blocks hblocks i.castSucc : ℝ) ≤
      (unitGridPoint blocks hblocks i.succ : ℝ) :=
    (unitGridPoint_strictMono blocks hblocks i.castSucc_lt_succ).le
  rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
  rw [unitGridPoint_coe, unitGridPoint_coe]
  have hsucc : (i.succ : ℝ) = (i.castSucc : ℝ) + 1 := by
    norm_num [Fin.val_succ, Fin.val_castSucc]
  rw [hsucc]
  have hblocksR : (blocks : ℝ) ≠ 0 := by exact_mod_cast hblocks.ne'
  field_simp
  ring

private theorem unitGridPoint_pair_distance_lower
    (blocks : ℕ) (hblocks : 0 < blocks) {i j : Fin (blocks + 1)} (hij : i ≠ j) :
    1 / (blocks : ℝ) ≤ dist (unitGridPoint blocks hblocks i)
      (unitGridPoint blocks hblocks j) := by
  have hforward {i j : Fin (blocks + 1)} (hij : i < j) :
      1 / (blocks : ℝ) ≤ dist (unitGridPoint blocks hblocks i)
        (unitGridPoint blocks hblocks j) := by
    let k : Fin blocks := ⟨i.val, by omega⟩
    have hk : k.castSucc = i := by apply Fin.ext; rfl
    have hks : k.succ ≤ j := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [Fin.val_succ]
      exact Fin.lt_def.mp hij
    have hstep := unitGridPoint_step_distance blocks hblocks k
    rw [hk] at hstep
    have hmono1 : unitGridPoint blocks hblocks i ≤
        unitGridPoint blocks hblocks k.succ := by
      rw [← hk]
      exact (unitGridPoint_strictMono blocks hblocks k.castSucc_lt_succ).le
    have hmono2 : unitGridPoint blocks hblocks k.succ ≤ unitGridPoint blocks hblocks j :=
      (unitGridPoint_strictMono blocks hblocks).monotone hks
    calc
      1 / (blocks : ℝ) = dist (unitGridPoint blocks hblocks i)
          (unitGridPoint blocks hblocks k.succ) := hstep.symm
      _ ≤ dist (unitGridPoint blocks hblocks i) (unitGridPoint blocks hblocks j) :=
        unitInterval_dist_le_of_subintervals le_rfl hmono1 hmono2
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hforward hij
  · simpa [dist_comm] using hforward hji

private theorem exists_unitGridPoint_between
    {blocks : ℕ} (hblocks : 0 < blocks) {p q : unitInterval} {c : ℝ}
    (hc : 0 ≤ c)
    (hwidth : 2 * (c + 1 / (blocks : ℝ)) < (q : ℝ) - (p : ℝ)) :
    ∃ j : Fin (blocks + 1), (p : ℝ) + c < unitGridPoint blocks hblocks j ∧
      (unitGridPoint blocks hblocks j : ℝ) < (q : ℝ) - c := by
  have hblocksR : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
  let raw := (p : ℝ) + c
  let k := Nat.floor (raw * (blocks : ℝ)) + 1
  have hraw : 0 ≤ raw := by dsimp [raw]; linarith [(p : unitInterval).property.1]
  have hmul_nonneg : 0 ≤ raw * (blocks : ℝ) := mul_nonneg hraw hblocksR.le
  have hfloor_le : (Nat.floor (raw * (blocks : ℝ)) : ℝ) ≤ raw * (blocks : ℝ) :=
    Nat.floor_le hmul_nonneg
  have hfloor_lt : raw * (blocks : ℝ) <
      (Nat.floor (raw * (blocks : ℝ)) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hk_lower : raw * (blocks : ℝ) < (k : ℝ) := by
    dsimp [k]
    push_cast
    exact hfloor_lt
  have hk_upper : (k : ℝ) ≤ (raw + 1 / (blocks : ℝ)) * (blocks : ℝ) := by
    have hkcast : (k : ℝ) =
        (Nat.floor (raw * (blocks : ℝ)) : ℝ) + 1 := by simp [k]
    have hmul : (raw + 1 / (blocks : ℝ)) * (blocks : ℝ) =
        raw * (blocks : ℝ) + 1 := by
      field_simp [hblocksR.ne']
    rw [hkcast, hmul]
    linarith [hfloor_le]
  have hleft : raw < (k : ℝ) / (blocks : ℝ) :=
    (lt_div_iff₀ hblocksR).2 (by simpa [raw, mul_comm] using hk_lower)
  have hright : (k : ℝ) / (blocks : ℝ) ≤
      raw + 1 / (blocks : ℝ) := (div_le_iff₀ hblocksR).2 hk_upper
  have hlast : (k : ℝ) / (blocks : ℝ) < (q : ℝ) - c := by
    dsimp [raw] at hleft hright
    linarith [hwidth, hblocksR]
  have hltOne : (k : ℝ) / (blocks : ℝ) < 1 :=
    lt_of_lt_of_le hlast (by linarith [(q : unitInterval).property.2])
  have hk_real : (k : ℝ) < (blocks : ℝ) :=
    by simpa using (div_lt_iff₀ hblocksR).mp hltOne
  have hk_nat : k < blocks := by exact_mod_cast hk_real
  let j : Fin (blocks + 1) := ⟨k, by omega⟩
  have hjval : (unitGridPoint blocks hblocks j : ℝ) = (k : ℝ) / (blocks : ℝ) := by
    rw [unitGridPoint_coe]
  refine ⟨j, ?_, ?_⟩
  · rw [hjval]
    exact hleft
  · rw [hjval]
    exact hlast

/-- The pathwise converse to the double-excursion criterion, with endpoint
oscillation controlled separately. For `0 < delta ≤ 1`, a path satisfying
both controls admits a finite oscillation partition with mesh at least
`delta / 16` and cell oscillation at most `5 * epsilon`. The construction
retains every interior jump larger than `2 * epsilon`, then keeps the uniform
grid points separated from those jumps. -/
theorem HasDoubleExcursionBound.exists_oscillation_partition
    {E : Type*} [PseudoMetricSpace E]
    {path : CadlagPath unitInterval E} {delta epsilon : ℝ}
    (hdouble : HasDoubleExcursionBound path delta epsilon)
    (hend : HasEndpointOscillationBound path delta epsilon)
    (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (hepsilon : 0 < epsilon) :
    ∃ partition : OscillationPartition,
      delta / 16 ≤ partition.mesh ∧
        OscillationBoundedOnPartition partition path (5 * epsilon) := by
  classical
  let large : Set unitInterval := {t | t ≠ ⊥ ∧ t ≠ ⊤ ∧
    2 * epsilon < dist (Function.leftLim (fun s : unitInterval => path s) t) (path t)}
  have hlargeFinite : large.Finite := by
    apply (path.isCadlag_toFun.finite_jumpTimesAbove
      (epsilon := 2 * epsilon) (by positivity)).subset
    intro t ht
    exact ⟨ht.1, ht.2.2⟩
  let largePoints : Finset unitInterval := hlargeFinite.toFinset
  have mem_largePoints {t : unitInterval} : t ∈ largePoints ↔ t ∈ large := by
    simp [largePoints]
  have hlargeAway {t : unitInterval} (ht : t ∈ large) :
      delta ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1 - delta := by
    rcases ht with ⟨_, httop, hjump⟩
    exact hend.largeJump_awayFromEndpoints hepsilon httop hjump
  have hlargeSeparated {s t : unitInterval} (hs : s ∈ large) (ht : t ∈ large)
      (hne : s ≠ t) : delta ≤ dist s t := by
    rcases hs with ⟨hsbot, hstop, hsjump⟩
    rcases ht with ⟨htbot, httop, htjump⟩
    exact hdouble.largeJumpsSeparated hepsilon hsbot hstop htbot httop hne hsjump htjump
  let blocks : ℕ := Nat.floor (4 / delta)
  have hfloor_nonneg : 0 ≤ 4 / delta := by positivity
  have hfloor_le : (blocks : ℝ) ≤ 4 / delta := by
    dsimp [blocks]
    exact Nat.floor_le hfloor_nonneg
  have hfloor_lt : 4 / delta < (blocks : ℝ) + 1 := by
    dsimp [blocks]
    exact Nat.lt_floor_add_one _
  have hdeltaInv : 1 ≤ 1 / delta := by
    apply (le_div_iff₀ hdelta).2
    nlinarith [hdelta_le_one]
  have hfour : 4 ≤ 4 / delta := by
    apply (le_div_iff₀ hdelta).2
    nlinarith [hdelta_le_one]
  have hblocksLarge : 3 < (blocks : ℝ) := by linarith
  have hblocks : 0 < blocks := by exact_mod_cast (by linarith : (0 : ℝ) < blocks)
  have hblocksR : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
  have hblocksDeltaUpper : (blocks : ℝ) * delta ≤ 4 :=
    (le_div_iff₀ hdelta).mp hfloor_le
  have hblocksDeltaLower : 3 < (blocks : ℝ) * delta := by
    have hfourEq : 4 / delta = 3 / delta + 1 / delta := by
      field_simp [hdelta.ne']
      ring
    have hthree : 3 / delta ≤ 4 / delta - 1 := by
      rw [hfourEq]
      linarith [hdeltaInv]
    have hfloorLower : 4 / delta - 1 < (blocks : ℝ) := by linarith [hfloor_lt]
    have hblocksLower : 3 / delta < (blocks : ℝ) := lt_of_le_of_lt hthree hfloorLower
    exact (div_lt_iff₀ hdelta).mp hblocksLower
  have hstepLower : delta / 4 ≤ 1 / (blocks : ℝ) := by
    have hdeltaN : delta ≤ 4 / (blocks : ℝ) :=
      (le_div_iff₀ hblocksR).2 (by nlinarith [hblocksDeltaUpper])
    calc
      delta / 4 ≤ (4 / (blocks : ℝ)) / 4 :=
        div_le_div_of_nonneg_right hdeltaN (by norm_num)
      _ = 1 / (blocks : ℝ) := by field_simp [hblocksR.ne']
  have hstepUpper : 1 / (blocks : ℝ) < delta / 3 := by
    apply (div_lt_iff₀ hblocksR).2
    nlinarith [hblocksDeltaLower]
  let gap := delta / 16
  have hgap_nonneg : 0 ≤ gap := by dsimp [gap]; linarith
  have hgap_pos : 0 < gap := by dsimp [gap]; positivity
  have hgap_le_delta : gap ≤ delta := by dsimp [gap]; linarith
  have hgap_le_step : gap ≤ 1 / (blocks : ℝ) := by
    dsimp [gap]
    linarith
  have hgridWindow : 2 * (gap + 1 / (blocks : ℝ)) < delta := by
    dsimp [gap]
    nlinarith [hstepUpper, hdelta]
  let goodIndices : Finset (Fin (blocks + 1)) := Finset.univ.filter fun j =>
    ∀ t ∈ large, gap ≤ dist (unitGridPoint blocks hblocks j) t
  let goodPoints : Finset unitInterval := goodIndices.image (unitGridPoint blocks hblocks)
  let zero : Fin (blocks + 1) := ⟨0, by omega⟩
  let last : Fin (blocks + 1) := ⟨blocks, by omega⟩
  have hzeroTime : unitGridPoint blocks hblocks zero = ⊥ := by
    apply Subtype.ext
    rw [unitGridPoint_coe]
    simp [zero]
  have hlastTime : unitGridPoint blocks hblocks last = ⊤ := by
    apply Subtype.ext
    rw [unitGridPoint_coe]
    change (blocks : ℝ) / (blocks : ℝ) = 1
    field_simp [hblocksR.ne']
  have hzeroGood : zero ∈ goodIndices := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro t ht
    have haway := hlargeAway ht
    rw [hzeroTime, unitInterval_dist_bot_eq]
    exact hgap_le_delta.trans haway.1
  have hlastGood : last ∈ goodIndices := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro t ht
    have haway := hlargeAway ht
    rw [hlastTime, unitInterval_dist_top_eq]
    have hdist : delta ≤ 1 - (t : ℝ) := by linarith [haway.2]
    exact hgap_le_delta.trans hdist
  have hbottomGood : (⊥ : unitInterval) ∈ goodPoints :=
    Finset.mem_image.mpr ⟨zero, hzeroGood, hzeroTime⟩
  have htopGood : (⊤ : unitInterval) ∈ goodPoints :=
    Finset.mem_image.mpr ⟨last, hlastGood, hlastTime⟩
  let pointsSet := largePoints ∪ goodPoints
  have hbottomSet : (⊥ : unitInterval) ∈ pointsSet :=
    Finset.mem_union.mpr (Or.inr hbottomGood)
  have htopSet : (⊤ : unitInterval) ∈ pointsSet :=
    Finset.mem_union.mpr (Or.inr htopGood)
  have hgoodDistance {x : unitInterval} (hx : x ∈ goodPoints)
      {t : unitInterval} (ht : t ∈ large) : gap ≤ dist x t := by
    obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hx
    have hjgood := (Finset.mem_filter.mp hj).2
    rw [← hjx]
    exact hjgood t ht
  have hremovedGrid {j : Fin (blocks + 1)}
      (hnot : unitGridPoint blocks hblocks j ∉ goodPoints) :
      ∃ t ∈ large, dist (unitGridPoint blocks hblocks j) t < gap := by
    by_contra hnone
    push Not at hnone
    have hgood : ∀ t ∈ large, gap ≤ dist (unitGridPoint blocks hblocks j) t := by
      intro t ht
      exact hnone t ht
    have hj : j ∈ goodIndices := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood⟩
    exact hnot (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  have hpointSeparated {x y : unitInterval} (hx : x ∈ pointsSet)
      (hy : y ∈ pointsSet) (hne : x ≠ y) : gap ≤ dist x y := by
    rcases Finset.mem_union.mp hx with hxLarge | hxGood
    · rcases Finset.mem_union.mp hy with hyLarge | hyGood
      · exact hgap_le_delta.trans (hlargeSeparated
          (mem_largePoints.mp hxLarge) (mem_largePoints.mp hyLarge) hne)
      · have h := hgoodDistance hyGood (mem_largePoints.mp hxLarge)
        simpa [dist_comm] using h
    · rcases Finset.mem_union.mp hy with hyLarge | hyGood
      · have h := hgoodDistance hxGood (mem_largePoints.mp hyLarge)
        simpa [dist_comm] using h
      · obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hxGood
        obtain ⟨j, hj, hjy⟩ := Finset.mem_image.mp hyGood
        have hij : i ≠ j := by
          intro heq
          apply hne
          calc
            x = unitGridPoint blocks hblocks i := hix.symm
            _ = unitGridPoint blocks hblocks j := by rw [heq]
            _ = y := hjy
        have hgrid := unitGridPoint_pair_distance_lower blocks hblocks hij
        calc
          gap ≤ 1 / (blocks : ℝ) := hgap_le_step
          _ ≤ dist (unitGridPoint blocks hblocks i) (unitGridPoint blocks hblocks j) := hgrid
          _ = dist x y := by rw [hix, hjy]

  obtain ⟨partition, hpartitionRange, hpartitionMesh⟩ :=
    OscillationPartition.exists_ofFinset pointsSet hbottomSet htopSet
  have hnoPointBetween {i : Fin partition.size} {z : unitInterval}
      (hz : z ∈ pointsSet)
      (hpz : partition.points i.castSucc < z)
      (hzq : z < partition.points i.succ) : False := by
    have hzRange : z ∈ Set.range partition.points := by
      rw [hpartitionRange]
      exact hz
    obtain ⟨j, hj⟩ := hzRange
    have hleft : i.castSucc.val < j.val := by
      by_contra hnot
      have hjle : j ≤ i.castSucc := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt hnot)
      have hmono := partition.strictMono_points.monotone hjle
      have hzle : z ≤ partition.points i.castSucc := by rw [← hj]; exact hmono
      exact (not_le_of_gt hpz) hzle
    have hright : j.val < i.succ.val := by
      by_contra hnot
      have hle : i.succ ≤ j := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt hnot)
      have hmono := partition.strictMono_points.monotone hle
      have hqle : partition.points i.succ ≤ z := by rw [← hj]; exact hmono
      exact (not_le_of_gt hzq) hqle
    have hleftVal : i.castSucc.val = i.val := by simp
    have hrightVal : i.succ.val = i.val + 1 := by simp
    omega
  have hgapLower (i : Fin partition.size) :
      gap ≤ dist (partition.points i.castSucc) (partition.points i.succ) := by
    have hleftSet : partition.points i.castSucc ∈ pointsSet := by
      have hrange : partition.points i.castSucc ∈ Set.range partition.points :=
        ⟨i.castSucc, rfl⟩
      rw [hpartitionRange] at hrange
      exact hrange
    have hrightSet : partition.points i.succ ∈ pointsSet := by
      have hrange : partition.points i.succ ∈ Set.range partition.points :=
        ⟨i.succ, rfl⟩
      rw [hpartitionRange] at hrange
      exact hrange
    have hne : partition.points i.castSucc ≠ partition.points i.succ :=
      ne_of_lt (partition.strictMono_points i.castSucc_lt_succ)
    exact hpointSeparated hleftSet hrightSet hne
  have hgapUpper (i : Fin partition.size) :
      dist (partition.points i.castSucc) (partition.points i.succ) < delta := by
    let p := partition.points i.castSucc
    let q := partition.points i.succ
    have hpq : p < q := by dsimp [p, q]; exact partition.strictMono_points i.castSucc_lt_succ
    have hdistEq : dist p q = (q : ℝ) - (p : ℝ) :=
      unitInterval_dist_eq_coe_sub hpq.le
    by_contra hnot
    have hdeltaDist : delta ≤ dist p q := le_of_not_gt hnot
    have hwidth : 2 * (gap + 1 / (blocks : ℝ)) < (q : ℝ) - (p : ℝ) := by
      rw [← hdistEq]
      exact hgridWindow.trans_le hdeltaDist
    obtain ⟨j, hpr, hrq⟩ := exists_unitGridPoint_between hblocks hgap_nonneg hwidth
    let r := unitGridPoint blocks hblocks j
    have hprCoord : (p : ℝ) + gap < (r : ℝ) := by
      simpa [r, unitGridPoint_coe] using hpr
    have hrqCoord : (r : ℝ) < (q : ℝ) - gap := by
      simpa [r, unitGridPoint_coe] using hrq
    have hpr' : p < r := by
      apply Subtype.coe_lt_coe.mpr
      exact (le_add_of_nonneg_right hgap_nonneg).trans_lt hprCoord
    have hrq' : r < q := by
      apply Subtype.coe_lt_coe.mpr
      exact hrqCoord.trans (sub_lt_self _ hgap_pos)
    have hrNotGood : r ∉ goodPoints := by
      intro hrGood
      have hrSet : r ∈ pointsSet := Finset.mem_union.mpr (Or.inr hrGood)
      exact hnoPointBetween hrSet hpr' hrq'
    obtain ⟨t, htLarge, hrt⟩ := hremovedGrid hrNotGood
    have hpt : p < t := by
      by_contra hnot
      have htp : t ≤ p := le_of_not_gt hnot
      have hprLower : gap < dist p r := by
        rw [unitInterval_dist_eq_coe_sub hpr'.le]
        linarith [hprCoord]
      have hdistMono : dist p r ≤ dist t r :=
        unitInterval_dist_le_of_subintervals htp hpr'.le le_rfl
      have : dist t r < gap := by simpa [dist_comm] using hrt
      linarith
    have htq : t < q := by
      by_contra hnot
      have hqt : q ≤ t := le_of_not_gt hnot
      have hrqLower : gap < dist r q := by
        rw [unitInterval_dist_eq_coe_sub hrq'.le]
        linarith [hrqCoord]
      have hdistMono : dist r q ≤ dist r t :=
        unitInterval_dist_le_of_subintervals le_rfl hrq'.le hqt
      have : dist r t < gap := by simpa [dist_comm] using hrt
      linarith
    have htSet : t ∈ pointsSet :=
      Finset.mem_union.mpr (Or.inl (mem_largePoints.mpr htLarge))
    exact hnoPointBetween htSet hpt htq
  have hmesh : gap ≤ partition.mesh := by
    rw [hpartitionMesh]
    change gap ≤ (OscillationPartition.finitePointGaps partition.points).min'
      (OscillationPartition.finitePointGaps_nonempty partition.size_pos partition.points)
    apply Finset.le_min'
    intro d hd
    obtain ⟨i, -, hdist⟩ := Finset.mem_image.mp hd
    rw [← hdist]
    exact hgapLower i
  have hosc : OscillationBoundedOnPartition partition path (5 * epsilon) := by
    intro s t hsTop htTop hindex
    let i := partition.index s
    let p := partition.points i.castSucc
    let q := partition.points i.succ
    have htIndex : partition.index t = i := by simpa [i] using hindex.symm
    have hps : p ≤ s := partition.index_lower s
    have hpt : p ≤ t := by
      change partition.points i.castSucc ≤ t
      rw [← htIndex]
      exact partition.index_lower t
    have hsq : s < q := by
      rcases partition.index_upper s with hnext | hlast
      · simpa [i, q] using hnext
      · have hqtop : q = ⊤ := by
          have hsucc : (partition.index s).succ = Fin.last partition.size := by
            apply Fin.ext
            simp only [Fin.val_succ, Fin.val_last]
            omega
          dsimp [q, i]
          rw [hsucc]
          simpa [Fin.last] using partition.last
        rw [hqtop]
        exact lt_top_iff_ne_top.mpr hsTop
    have htq : t < q := by
      rcases partition.index_upper t with hnext | hlast
      · simpa [i, q, htIndex] using hnext
      · have hqtop : q = ⊤ := by
          have hsucc : (partition.index t).succ = Fin.last partition.size := by
            apply Fin.ext
            simp only [Fin.val_succ, Fin.val_last]
            omega
          dsimp [q, i]
          rw [hindex]
          rw [hsucc]
          simpa [Fin.last] using partition.last
        rw [hqtop]
        exact lt_top_iff_ne_top.mpr htTop
    have hpq : p < q := by dsimp [p, q]; exact partition.strictMono_points i.castSucc_lt_succ
    have hspan : dist p q < delta := by
      dsimp [p, q]
      exact hgapUpper i
    have hordered : ∀ x y : unitInterval, p ≤ x → x ≤ y → y < q →
        dist (path x) (path y) ≤ 5 * epsilon := by
      intro x y hpx hxy hyq
      by_cases hqtop : q = ⊤
      · have hpcoord : 1 - delta < (p : ℝ) := by
          have hdist : dist p q = 1 - (p : ℝ) := by
            rw [hqtop]
            simpa [dist_comm] using unitInterval_dist_top_eq p
          rw [hdist] at hspan
          linarith
        have hyTopLt : y < ⊤ := by simpa [hqtop] using hyq
        have hxTop : x ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hxy hyTopLt)
        have hyTop : y ≠ ⊤ := ne_of_lt hyTopLt
        have hxRight : 1 - delta < (x : ℝ) := lt_of_lt_of_le hpcoord (by exact_mod_cast hpx)
        have hyRight : 1 - delta < (y : ℝ) := lt_of_lt_of_le hpcoord (by exact_mod_cast (hpx.trans hxy))
        have hbound := hend.2 x y hxTop hyTop hxRight hyRight
        exact hbound.trans (by nlinarith [hepsilon])
      · have hjump : ∀ z, p < z → z < q →
            dist (Function.leftLim (fun v : unitInterval => path v) z) (path z) ≤ 2 * epsilon := by
          intro z hpz hzq
          by_contra hnot
          have hj : 2 * epsilon <
              dist (Function.leftLim (fun v : unitInterval => path v) z) (path z) :=
            lt_of_not_ge hnot
          have hbot : z ≠ ⊥ := ne_of_gt (lt_of_le_of_lt bot_le hpz)
          have htop' : z ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hzq le_top)
          have hlarge : z ∈ large := ⟨hbot, htop', hj⟩
          have hzSet : z ∈ pointsSet :=
            Finset.mem_union.mpr (Or.inl (mem_largePoints.mpr hlarge))
          exact hnoPointBetween hzSet hpz hzq
        exact hdouble.oscillation_le_of_jumpBound hepsilon hqtop hspan hjump
          x y hpx hxy hyq
    rcases le_total s t with hst | hts
    · exact hordered s t hps hst htq
    · simpa [dist_comm] using hordered t s hpt hts hsq
  exact ⟨partition, by simpa [gap] using hmesh, hosc⟩

end Skorokhod

end

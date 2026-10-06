/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Order.Interval.UniformGrid
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.Image
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Arithmetic for finite rational grids

This module contains the denominator arithmetic used to place bounded finite
rational families on a unit grid. It has no topology or interval-adapter
dependencies.
-/

@[expose] public section

namespace RationalGrid.Arithmetic

/- Affine normalization used internally to transport a bounded interval to
the unit interval. -/
private def normalize (left right q : ℚ) : ℚ := (q - left) / (right - left)

private theorem normalize_mem_unit_interval {left right q : ℚ} (hstrict : left < right)
    (hq : left ≤ q ∧ q ≤ right) : 0 ≤ normalize left right q ∧
      normalize left right q ≤ 1 := by
  have hden : 0 < right - left := sub_pos.mpr hstrict
  constructor
  · exact div_nonneg (sub_nonneg.mpr hq.1) hden.le
  · apply (div_le_one hden).2
    exact sub_le_sub_right hq.2 left

private def denominator (q : ℚ) : ℕ := q.den

private theorem denominator_pos (q : ℚ) : 0 < denominator q :=
  Rat.den_pos _

private def numerator (q : ℚ) : ℕ := q.num.toNat

private theorem num_nonneg (q : ℚ) (hq : 0 ≤ q) : 0 ≤ q.num :=
  Rat.num_nonneg.mpr hq

private theorem cast_eq_numerator_div_denominator (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) = numerator q / denominator q := by
  rw [show (q : ℝ) = ((q : ℚ) : ℝ) by rfl, Rat.cast_def]
  unfold numerator denominator
  congr 1
  norm_cast
  exact (Int.toNat_of_nonneg (num_nonneg q hq)).symm

private theorem numerator_le_denominator (q : ℚ) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) : numerator q ≤ denominator q := by
  have hcast : (q : ℝ) ≤ 1 := by
    simpa using (Rat.cast_le (K := ℝ)).2 hq1
  rw [cast_eq_numerator_div_denominator q hq0,
    div_le_one (by exact_mod_cast denominator_pos q)] at hcast
  exact_mod_cast hcast

private def commonDenominator (I : Finset ℚ) : ℕ :=
  I.lcm denominator

private theorem commonDenominator_pos (I : Finset ℚ) :
    0 < commonDenominator I := by
  apply Nat.pos_of_ne_zero
  rw [commonDenominator, Finset.lcm_ne_zero_iff]
  intro q hq
  exact Nat.ne_of_gt (denominator_pos q)

private theorem denominator_dvd_commonDenominator
    {I : Finset ℚ} {q : I} :
    denominator q.1 ∣ commonDenominator I := by
  rw [commonDenominator]
  exact Finset.dvd_lcm q.2

/-- A finite rational family lying in `[0, 1]` is represented by one unit
uniform grid. This is an arithmetic construction for use by the rational-grid
and bounded-interval adapters. -/
theorem exists_unit_uniformGrid_of_finset (I : Finset ℚ)
    (hI : ∀ q ∈ I, 0 ≤ q ∧ q ≤ 1) :
    ∃ grid : UniformGrid ℝ, grid.left = 0 ∧ grid.right = 1 ∧
      ∃ index : I → grid.Index,
      ∀ i : I, (i.1 : ℝ) = grid.point (index i) := by
  let blocks := commonDenominator I
  have hblocks : 0 < blocks := commonDenominator_pos I
  let indexValue : I → ℕ := fun i ↦
    numerator i.1 * (blocks / denominator i.1)
  have hindex_le (i : I) : indexValue i ≤ blocks := by
    have hdvd : denominator i.1 ∣ blocks := denominator_dvd_commonDenominator
    calc
      indexValue i ≤ denominator i.1 * (blocks / denominator i.1) := by
        dsimp only [indexValue]
        gcongr
        exact numerator_le_denominator i.1 (hI i.1 i.2).1 (hI i.1 i.2).2
      _ = blocks := Nat.mul_div_cancel' hdvd
  let grid := UniformGrid.unit (K := ℝ) blocks hblocks
  let index : I → grid.Index := fun i ↦
    ⟨indexValue i, Nat.lt_succ_iff.mpr (hindex_le i)⟩
  refine ⟨grid, rfl, rfl, index, fun (i : I) ↦ ?_⟩
  have hdvd : denominator i.1 ∣ blocks := denominator_dvd_commonDenominator
  have hquotient : 0 < blocks / denominator i.1 := by
    exact Nat.div_pos (Nat.le_of_dvd hblocks hdvd) (denominator_pos i.1)
  rw [cast_eq_numerator_div_denominator i.1 (hI i.1 i.2).1]
  change (numerator i.1 : ℝ) / denominator i.1 = grid.point (index i)
  have hunit : grid.point (index i) = (index i : ℝ) / blocks := by
    simpa [grid] using UniformGrid.unit_point (K := ℝ) blocks hblocks (index i)
  rw [hunit]
  dsimp only [index, indexValue]
  push_cast
  rw [show (blocks : ℝ) =
      (denominator i.1 : ℝ) * (blocks / denominator i.1 : ℕ) by
    exact_mod_cast (Nat.mul_div_cancel' hdvd).symm]
  have hdenR : (denominator i.1 : ℝ) ≠ 0 := by
    exact_mod_cast (denominator_pos i.1).ne'
  have hquotientR : (blocks / denominator i.1 : ℕ) ≠ 0 :=
    Nat.ne_of_gt hquotient
  have hquotientR' : ((blocks / denominator i.1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hquotientR
  field_simp [hdenR, hquotientR']

/-- Every finite family of rational points in a fixed bounded interval is
represented on a uniform real grid with the given endpoints. -/
theorem exists_uniformGrid_of_finset_mem_Icc {left right : ℚ}
    (hleft : left ≤ right) (I : Finset ℚ)
    (hI : ∀ q ∈ I, left ≤ q ∧ q ≤ right) :
    ∃ grid : UniformGrid ℝ, grid.left = left ∧ grid.right = right ∧
      ∃ index : I → grid.Index,
      ∀ i : I, (i.1 : ℝ) = grid.point (index i) := by
  by_cases hEq : right = left
  · let grid : UniformGrid ℝ :=
      { left := left
        right := right
        blocks := 1
        left_le_right := by simpa using (Rat.cast_le (K := ℝ)).2 hleft
        blocks_pos := Nat.zero_lt_one }
    let index : I → grid.Index := fun _ => ⟨0, by simp [grid]⟩
    refine ⟨grid, rfl, rfl, index, fun i ↦ ?_⟩
    have hi : i.1 = left := by
      apply le_antisymm
      · simpa [hEq] using (hI i.1 i.2).2
      · exact (hI i.1 i.2).1
    simp [grid, UniformGrid.point, index, hi, hEq]
  · have hstrict : left < right := lt_of_le_of_ne hleft (Ne.symm hEq)
    let J : Finset ℚ := I.attach.image (fun q => normalize left right q.1)
    obtain ⟨unitGrid, hunitLeft, hunitRight, unitIndex, hunit⟩ :=
      exists_unit_uniformGrid_of_finset J (by
        intro q hq
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hq
        exact normalize_mem_unit_interval hstrict (hI x.1 x.2))
    let grid : UniformGrid ℝ :=
      { left := left
        right := right
        blocks := unitGrid.blocks
        left_le_right := by simpa using (Rat.cast_le (K := ℝ)).2 hleft
        blocks_pos := unitGrid.blocks_pos }
    let index : I → grid.Index := fun i ↦
      unitIndex ⟨normalize left right i.1,
        Finset.mem_image.mpr ⟨i, Finset.mem_attach I i, rfl⟩⟩
    refine ⟨grid, rfl, rfl, index, fun i ↦ ?_⟩
    let j : J := ⟨normalize left right i.1,
      Finset.mem_image.mpr ⟨i, Finset.mem_attach I i, rfl⟩⟩
    have hnormalized :
        (j.1 : ℝ) = unitGrid.point (unitIndex j) := hunit j
    have hunitcoord : (unitGrid.point (unitIndex j) : ℝ) =
        ((i.1 : ℚ) - left) / (right - left) := by
      rw [← hnormalized]
      change (normalize left right i.1 : ℝ) = _
      simp [normalize, Rat.cast_sub, Rat.cast_div]
    change (i.1 : ℝ) = grid.point (index i)
    rw [show grid.point (index i) =
        left + unitGrid.point (unitIndex j) * (right - left) by
      simp [grid, index, j, UniformGrid.point, hunitLeft, hunitRight]]
    rw [hunitcoord]
    have hdenR : (right : ℝ) - left ≠ 0 := by
      rw [← Rat.cast_sub]
      exact Rat.cast_ne_zero.mpr (sub_ne_zero.mpr hEq)
    rw [div_mul_cancel₀ _ hdenR]
    ring

end RationalGrid.Arithmetic

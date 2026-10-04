/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Order.Interval.UniformGrid

/-!
# Rational coordinates and finite grids

This file contains the deterministic rational-coordinate infrastructure used
by several path constructions.  The bounded interval is a parameter of the
API; the unit interval is only the convenient specialization
`RationalUnitInterval`.
-/

@[expose] public section

open Set

namespace RationalGrid

/-- Rational points in a (possibly empty) rational interval. -/
abbrev RationalInterval (left right : ℚ) :=
  Set.Icc left right

/-- Rational points in the unit interval. -/
abbrev RationalUnitInterval := RationalInterval 0 1

/-- The real coordinate represented by a rational interval point. -/
def coe {left right : ℚ} (q : RationalInterval left right) : ℝ :=
  (q : ℚ)

@[simp] theorem coe_mk {left right : ℚ} (q : ℚ) (hq : left ≤ q ∧ q ≤ right) :
    coe (⟨q, hq⟩ : RationalInterval left right) = (q : ℝ) := rfl

/-- Positive denominator of a nonnegative rational unit-interval point. -/
def denominator (q : RationalUnitInterval) : ℕ :=
  (q : ℚ).den

theorem denominator_pos (q : RationalUnitInterval) :
    0 < denominator q :=
  Rat.den_pos _

/-- Natural numerator of a nonnegative rational unit-interval point. -/
def numerator (q : RationalUnitInterval) : ℕ :=
  (q : ℚ).num.toNat

theorem num_nonneg (q : RationalUnitInterval) :
    0 ≤ (q : ℚ).num := by
  exact Rat.num_nonneg.mpr q.property.1

theorem cast_eq_numerator_div_denominator
    (q : RationalUnitInterval) :
    (q : ℝ) = numerator q / denominator q := by
  rw [show (q : ℝ) = ((q : ℚ) : ℝ) by rfl, Rat.cast_def]
  unfold numerator denominator
  congr 1
  norm_cast
  exact (Int.toNat_of_nonneg (num_nonneg q)).symm

theorem numerator_le_denominator (q : RationalUnitInterval) :
    numerator q ≤ denominator q := by
  have hcast : (q : ℝ) ≤ 1 := by exact_mod_cast q.property.2
  rw [cast_eq_numerator_div_denominator,
    div_le_one (by exact_mod_cast denominator_pos q)] at hcast
  exact_mod_cast hcast

/-- A positive common denominator for a finite family of unit-interval points. -/
def commonDenominator (I : Finset RationalUnitInterval) : ℕ :=
  ∏ q ∈ I, denominator q

theorem commonDenominator_pos (I : Finset RationalUnitInterval) :
    0 < commonDenominator I := by
  unfold commonDenominator
  exact Finset.prod_pos fun q _ ↦ denominator_pos q

theorem denominator_dvd_commonDenominator
    {I : Finset RationalUnitInterval} (q : I) :
    denominator q ∣ commonDenominator I := by
  unfold commonDenominator
  exact Finset.dvd_prod_of_mem (fun q ↦ denominator q) q.property

/-- A finite family of unit-interval rational points is contained in one
finite uniform grid. -/
theorem exists_unit_uniformGrid_of_finset (I : Finset RationalUnitInterval) :
    ∃ grid : UniformGrid, grid.left = 0 ∧ grid.right = 1 ∧
      ∃ index : I → grid.Index,
      ∀ i : I, (coe (left := 0) (right := 1) i : ℝ) = grid.point (index i) := by
  let blocks := commonDenominator I
  have hblocks : 0 < blocks := commonDenominator_pos I
  let indexValue : I → ℕ := fun i ↦
    numerator i * (blocks / denominator i)
  have hindex_le (i : I) : indexValue i ≤ blocks := by
    have hdvd : denominator i ∣ blocks :=
      denominator_dvd_commonDenominator i
    calc
      indexValue i ≤ denominator i * (blocks / denominator i) := by
        dsimp only [indexValue]
        gcongr
        exact numerator_le_denominator i
      _ = blocks := Nat.mul_div_cancel' hdvd
  let grid := UniformGrid.unit blocks hblocks
  let index : I → grid.Index := fun i ↦
    ⟨indexValue i, Nat.lt_succ_iff.mpr (hindex_le i)⟩
  refine ⟨grid, rfl, rfl, index, fun (i : I) ↦ ?_⟩
  have hdvd : denominator i ∣ blocks :=
    denominator_dvd_commonDenominator i
  have hquotient : 0 < blocks / denominator i := by
    exact Nat.div_pos (Nat.le_of_dvd hblocks hdvd) (denominator_pos i)
  rw [show (coe (left := 0) (right := 1) i : ℝ) = (i : ℝ) by rfl,
    cast_eq_numerator_div_denominator]
  change (numerator i : ℝ) / denominator i = grid.point (index i)
  have hunit : grid.point (index i) = (index i : ℝ) / blocks := by
    simpa [grid] using UniformGrid.unit_point blocks hblocks (index i)
  rw [hunit]
  dsimp only [index, indexValue]
  push_cast
  rw [show (blocks : ℝ) =
      (denominator i : ℝ) * (blocks / denominator i : ℕ) by
    exact_mod_cast (Nat.mul_div_cancel' hdvd).symm]
  field_simp

/-! The generic interval statement is obtained by affine normalization to the
unit interval. -/

def normalize {left right : ℚ} (hleft : left ≤ right)
    (q : RationalInterval left right) : RationalUnitInterval :=
  ⟨((q : ℚ) - left) / (right - left), by
    have hnonneg : 0 ≤ (q : ℚ) - left := sub_nonneg.mpr q.property.1
    have hden : 0 ≤ right - left := sub_nonneg.mpr hleft
    constructor
    · exact div_nonneg hnonneg hden
    · by_cases hEq : right = left
      · simp [hEq, sub_self]
      · have hpos : 0 < right - left := sub_pos.mpr (lt_of_le_of_ne hleft (Ne.symm hEq))
        apply (div_le_one hpos).2
        exact sub_le_sub_right q.property.2 left⟩

theorem coe_normalize {left right : ℚ} (hleft : left ≤ right)
    (q : RationalInterval left right) :
    (normalize hleft q : ℚ) = ((q : ℚ) - left) / (right - left) := rfl

theorem normalize_injective {left right : ℚ} (hstrict : left < right) :
    Function.Injective (normalize (le_of_lt hstrict) :
      RationalInterval left right → RationalUnitInterval) := by
  intro p q hpq
  apply Subtype.ext
  have hden : right - left ≠ 0 := ne_of_gt (sub_pos.mpr hstrict)
  have hscaled := congrArg Subtype.val hpq
  simp only [normalize, Subtype.coe_mk] at hscaled
  field_simp [hden] at hscaled
  linarith

theorem exists_uniformGrid_of_finset
    {left right : ℚ} (hleft : left ≤ right)
    (I : Finset (RationalInterval left right)) :
    ∃ grid : UniformGrid, grid.left = left ∧ grid.right = right ∧
      ∃ index : I → grid.Index,
      ∀ i : I, (coe (left := left) (right := right) i : ℝ) =
        grid.point (index i) := by
  by_cases hEq : right = left
  · let grid : UniformGrid :=
      { left := left
        right := right
        blocks := 1
        left_le_right := by exact_mod_cast hleft
        blocks_pos := Nat.zero_lt_one }
    let index : I → grid.Index := fun _ => ⟨0, by simp [grid]⟩
    refine ⟨grid, rfl, rfl, index, fun i ↦ ?_⟩
    have hqi : (i : ℚ) = left := by
      apply le_antisymm
      · simpa [hEq] using i.1.property.2
      · exact i.1.property.1
    simp [coe, grid, UniformGrid.point, index, hqi, hEq]
  · have hstrict : left < right := lt_of_le_of_ne hleft (Ne.symm hEq)
    let hle : left ≤ right := le_of_lt hstrict
    let J : Finset RationalUnitInterval :=
      I.map ⟨normalize hle, normalize_injective hstrict⟩
    obtain ⟨unitGrid, hunitLeft, hunitRight, unitIndex, hunit⟩ :=
      exists_unit_uniformGrid_of_finset J
    let grid : UniformGrid :=
      { left := left
        right := right
        blocks := unitGrid.blocks
        left_le_right := by exact_mod_cast hleft
        blocks_pos := unitGrid.blocks_pos }
    let index : I → grid.Index := fun i ↦
      unitIndex ⟨normalize hle i,
        Finset.mem_map.mpr ⟨i, i.property, rfl⟩⟩
    refine ⟨grid, rfl, rfl, index, fun i ↦ ?_⟩
    let j : J := ⟨normalize hle i,
      Finset.mem_map.mpr ⟨i, i.property, rfl⟩⟩
    have hnormalized :
        (coe (left := 0) (right := 1) j : ℝ) = unitGrid.point (unitIndex j) :=
      hunit j
    have hunitcoord : (unitGrid.point (unitIndex j) : ℝ) =
        ((i : ℚ) - left) / (right - left) := by
      rw [← hnormalized]
      change ((normalize hle i : ℚ) : ℝ) = _
      simp [normalize]
    change (i : ℝ) = grid.point (index i)
    rw [show grid.point (index i) =
        left + unitGrid.point (unitIndex j) * (right - left) by
      simp [grid, index, j, UniformGrid.point, hunitLeft, hunitRight]
      ]
    rw [hunitcoord]
    have hdenR' : (right : ℝ) - left ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast hEq)
    rw [div_mul_cancel₀ _ hdenR']
    ring

end RationalGrid

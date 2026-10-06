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
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp

/-!
# Arithmetic for finite rational grids

This module contains the denominator arithmetic used to place bounded finite
rational families on a unit grid. It has no topology or interval-adapter
dependencies.
-/

@[expose] public section

namespace RationalGrid.Arithmetic

/-- Affine rational normalization for arithmetic grid constructions. -/
def normalize (left right q : ℚ) : ℚ := (q - left) / (right - left)

theorem normalize_mem_unit_interval {left right q : ℚ} (hstrict : left < right)
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

end RationalGrid.Arithmetic

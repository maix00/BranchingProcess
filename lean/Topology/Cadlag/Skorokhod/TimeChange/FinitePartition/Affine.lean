/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Affine interpolation for finite partitions

Linear interpolation on an interval and its basic order and displacement
bounds.
-/

@[expose] public section

namespace Skorokhod.TimeChange.FinitePartition

/-- Linear interpolation from `[a, b]` onto `[c, d]`. -/
noncomputable def affineInterpolate (a b c d x : ℝ) : ℝ :=
  c + (d - c) / (b - a) * (x - a)

/-- Linear interpolation maps the left endpoint to the left endpoint. -/
theorem affineInterpolate_left {a b c d : ℝ} :
    affineInterpolate a b c d a = c := by
  simp [affineInterpolate]

/-- Linear interpolation maps the right endpoint to the right endpoint. -/
theorem affineInterpolate_right {a b c d : ℝ} (hab : a < b) :
    affineInterpolate a b c d b = d := by
  unfold affineInterpolate
  rw [div_mul_cancel₀ (d - c)
    (sub_ne_zero.mpr (Ne.symm (ne_of_lt hab)))]
  ring

/-- Linear interpolation is strictly increasing when both intervals have
positive length. -/
theorem affineInterpolate_strictMono {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) :
    StrictMono (affineInterpolate a b c d) := by
  intro x y hxy
  unfold affineInterpolate
  have hslope : 0 < (d - c) / (b - a) :=
    div_pos (sub_pos.mpr hcd) (sub_pos.mpr hab)
  simpa [add_comm] using add_lt_add_left
    (mul_lt_mul_of_pos_left (sub_lt_sub_right hxy a) hslope) c

/-- Linear interpolation stays between its endpoint values. -/
theorem affineInterpolate_mem {a b c d x : ℝ}
    (hab : a < b) (hcd : c < d) (hax : a ≤ x) (hxb : x ≤ b) :
    c ≤ affineInterpolate a b c d x ∧ affineInterpolate a b c d x ≤ d := by
  have hslope : 0 < (d - c) / (b - a) :=
    div_pos (sub_pos.mpr hcd) (sub_pos.mpr hab)
  have hleft : 0 ≤ (d - c) / (b - a) * (x - a) :=
    mul_nonneg hslope.le (sub_nonneg.mpr hax)
  have hright :
      (d - c) / (b - a) * (x - a) ≤ (d - c) / (b - a) * (b - a) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hxb a) hslope.le
  constructor
  · unfold affineInterpolate
    linarith
  · calc
      affineInterpolate a b c d x ≤ c + (d - c) / (b - a) * (b - a) := by
        unfold affineInterpolate
        simpa [add_comm] using add_le_add_left hright c
      _ = d := by
        rw [div_mul_cancel₀ (d - c)
          (sub_ne_zero.mpr (Ne.symm (ne_of_lt hab)))]
        ring

/-- Interpolation is strictly below the right endpoint before the source
right endpoint. -/
theorem affineInterpolate_lt_right {a b c d x : ℝ}
    (hab : a < b) (hcd : c < d) (hx : x < b) :
    affineInterpolate a b c d x < d := by
  calc
    affineInterpolate a b c d x < affineInterpolate a b c d b :=
      affineInterpolate_strictMono hab hcd hx
    _ = d := affineInterpolate_right hab

/-- Interpolating on an interval and then on the reversed pair of intervals
returns the original point. -/
theorem affineInterpolate_swapped {a b c d x : ℝ}
    (hab : a < b) (hcd : c < d) :
    affineInterpolate c d a b (affineInterpolate a b c d x) = x := by
  unfold affineInterpolate
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hab))
  have hdc : d - c ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hcd))
  field_simp [hba, hdc]
  ring

/-- The displacement of an affine interpolation is bounded by the larger
displacement of its endpoints. -/
theorem affineInterpolate_distortion_le_max {a b c d x : ℝ}
    (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    |affineInterpolate a b c d x - x| ≤ max |c - a| |d - b| := by
  let θ := (x - a) / (b - a)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hab))
  have hθ_nonneg : 0 ≤ θ := by
    dsimp [θ]
    exact div_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hab.le)
  have hθ_le_one : θ ≤ 1 := by
    dsimp [θ]
    exact (div_le_one (sub_pos.mpr hab)).2 (sub_le_sub_right hxb a)
  have hformula : affineInterpolate a b c d x - x =
    (1 - θ) * (c - a) + θ * (d - b) := by
    dsimp [affineInterpolate, θ]
    field_simp [hba]; ring
  have hleft_nonneg : 0 ≤ 1 - θ := by linarith
  calc
    |affineInterpolate a b c d x - x| =
        |(1 - θ) * (c - a) + θ * (d - b)| := by rw [hformula]
    _ ≤ |(1 - θ) * (c - a)| + |θ * (d - b)| := abs_add_le _ _
    _ = (1 - θ) * |c - a| + θ * |d - b| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hleft_nonneg, abs_of_nonneg hθ_nonneg]
    _ ≤ (1 - θ) * max |c - a| |d - b| +
          θ * max |c - a| |d - b| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hleft_nonneg)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hθ_nonneg)
    _ = max |c - a| |d - b| := by ring

end Skorokhod.TimeChange.FinitePartition

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Bounded windows from two-sided measure mass

A real measure charging both open half-lines also charges a bounded positive
window and its reflected negative window, with common inner and outer radii.
-/

@[expose] public section

namespace MeasureTheory

open Set

/-- Positive mass on either side of a reference value yields bounded
windows for positive and negative corrections relative to that value. -/
theorem Measure.exists_twoSidedWindow_around_pos (μ : Measure ℝ)
    (v : ℝ) (habove : 0 < μ (Ioi v)) (hbelow : 0 < μ (Iio v)) :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧
      0 < μ (Ioo (v + r) (v + R)) ∧
      0 < μ (Ioo (v - R) (v - r)) := by
  obtain ⟨xp, hxp, hxpSupport⟩ := μ.nonempty_inter_support_of_pos habove
  obtain ⟨xn, hxn, hxnSupport⟩ := μ.nonempty_inter_support_of_pos hbelow
  have hxp0 : 0 < xp - v := sub_pos.mpr hxp
  have hxn0 : 0 < v - xn := sub_pos.mpr (show xn < v from hxn)
  let r : ℝ := min (xp - v) (v - xn) / 2
  let R : ℝ := max (xp - v) (v - xn) + 1
  have hr : 0 < r := by
    dsimp [r]
    exact half_pos (lt_min hxp0 hxn0)
  have hxpWindow : xp ∈ Ioo (v + r) (v + R) := by
    constructor
    · dsimp [r]
      linarith [min_le_left (xp - v) (v - xn)]
    · dsimp [R]
      linarith [le_max_left (xp - v) (v - xn)]
  have hxnWindow : xn ∈ Ioo (v - R) (v - r) := by
    constructor
    · dsimp [R]
      linarith [le_max_right (xp - v) (v - xn)]
    · dsimp [r]
      linarith [min_le_right (xp - v) (v - xn)]
  refine ⟨r, R, hr, ?_, ?_, ?_⟩
  · linarith [hxpWindow.1, hxpWindow.2]
  · exact (Measure.mem_support_iff_forall xp).mp hxpSupport _
      (isOpen_Ioo.mem_nhds hxpWindow)
  · exact (Measure.mem_support_iff_forall xn).mp hxnSupport _
      (isOpen_Ioo.mem_nhds hxnWindow)

end MeasureTheory

end

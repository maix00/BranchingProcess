/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Truncating real increments

This file is deterministic.  It defines the hard symmetric truncation used in
finite-second-moment invariance arguments and records its pointwise bounds.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- Keep an increment when its absolute value is at most `radius`, and replace
it by zero otherwise.  No positivity assumption is built into the definition. -/
noncomputable def truncatedIncrement (radius x : ℝ) : ℝ :=
  if |x| ≤ radius then x else 0

@[simp] theorem truncatedIncrement_of_abs_le {radius x : ℝ}
    (h : |x| ≤ radius) :
    truncatedIncrement radius x = x := by
  simp [truncatedIncrement, h]

@[simp] theorem truncatedIncrement_of_lt_abs {radius x : ℝ}
    (h : radius < |x|) :
    truncatedIncrement radius x = 0 := by
  simp [truncatedIncrement, not_le_of_gt h]

theorem measurable_truncatedIncrement (radius : ℝ) :
    Measurable (truncatedIncrement radius) := by
  unfold truncatedIncrement
  exact measurable_id.ite
    (measurableSet_le continuous_abs.measurable measurable_const) measurable_const

theorem abs_truncatedIncrement_le_abs (radius x : ℝ) :
    |truncatedIncrement radius x| ≤ |x| := by
  by_cases h : |x| ≤ radius <;> simp [truncatedIncrement, h]

theorem abs_truncatedIncrement_le {radius x : ℝ} (hradius : 0 ≤ radius) :
    |truncatedIncrement radius x| ≤ radius := by
  by_cases h : |x| ≤ radius
  · simp [truncatedIncrement, h]
  · simp [truncatedIncrement, h, hradius]

/-- The fourth power of a truncated increment is controlled by its original
second power times the squared truncation radius. -/
theorem truncatedIncrement_pow_four_le {radius x : ℝ} (hradius : 0 ≤ radius) :
    truncatedIncrement radius x ^ 4 ≤ radius ^ 2 * x ^ 2 := by
  by_cases h : |x| ≤ radius
  · rw [truncatedIncrement_of_abs_le h]
    have hs : x ^ 2 ≤ radius ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hradius]
      exact h
    calc
      x ^ 4 = x ^ 2 * x ^ 2 := by ring
      _ ≤ radius ^ 2 * x ^ 2 :=
        mul_le_mul_of_nonneg_right hs (sq_nonneg x)
  · rw [truncatedIncrement_of_lt_abs (lt_of_not_ge h)]
    simpa using mul_nonneg (sq_nonneg radius) (sq_nonneg x)

end ProbabilityTheory.RandomWalk

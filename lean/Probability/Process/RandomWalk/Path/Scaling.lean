/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.AdditivePath
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Probability.Process.RandomWalk.Path.Basic

import Mathlib.Tactic.FieldSimp

/-!
# Rescaled step paths

The rescaled right-continuous step path divides the first `⌊nt⌋` increments by
a spatial scale. This construction is deterministic; probability laws and
corridor events are developed separately.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- The normalized step path used in Mogulskii's theorem.  Its intended time
domain is `[0,1]`; defining it on all reals makes endpoint evaluation and
composition easier. -/
noncomputable def normalizedStepPath (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) (t : ℝ) : ℝ :=
  (scale n)⁻¹ * AdditivePath.displacement ⌊(n : ℝ) * t⌋₊ increment

@[simp] theorem normalizedStepPath_zero (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) :
    normalizedStepPath scale n increment 0 = 0 := by
  simp [normalizedStepPath]

/-- Evaluation of the normalized path at a fixed time is measurable as a
function of its increment path. -/
theorem normalizedStepPath_measurable (scale : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    Measurable (fun increment : ℕ → ℝ =>
      normalizedStepPath scale n increment t) := by
  exact measurable_const.mul (displacement_measurable _)

/-- At time one, the normalized path is the normalized `n`-step sum. -/
@[simp] theorem normalizedStepPath_one (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) :
    normalizedStepPath scale n increment 1 =
      (scale n)⁻¹ * AdditivePath.displacement n increment := by
  simp [normalizedStepPath]

/-- Evaluation on the `n`-step time grid recovers the corresponding partial
sum. -/
theorem normalizedStepPath_grid (scale : ℕ → ℝ) {n k : ℕ}
    (hn : 0 < n) (increment : ℕ → ℝ) :
    normalizedStepPath scale n increment ((k : ℝ) / n) =
      (scale n)⁻¹ * AdditivePath.displacement k increment := by
  rw [normalizedStepPath]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hgrid : (n : ℝ) * ((k : ℝ) / n) = k := by
    field_simp
  rw [hgrid, Nat.floor_natCast]


end ProbabilityTheory.RandomWalk

end

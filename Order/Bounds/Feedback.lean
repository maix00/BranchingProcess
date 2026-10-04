/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Deterministic feedback bounds

Alternating endpoint corrections keep scalar errors bounded. The block-path
estimate is stated for any parameter type equipped with a bounded real
coordinate; it does not depend on a particular path space.
-/

@[expose] public section

namespace Real

/-- If each increment corrects the sign of the current error by an amount
between `r` and `R`, endpoint errors never exceed `R`. -/
theorem feedback_endpoint_error_bound
    (e : ℕ → ℝ) (n : ℕ) (r R : ℝ)
    (hR : 0 ≤ R) (hr : 0 ≤ r) (he0 : e 0 = 0)
    (hstep : ∀ k < n,
      (0 ≤ e k → -R ≤ e (k + 1) - e k ∧ e (k + 1) - e k ≤ -r) ∧
      (e k < 0 → r ≤ e (k + 1) - e k ∧ e (k + 1) - e k ≤ R)) :
    ∀ k ≤ n, |e k| ≤ R := by
  intro k hk
  induction k with
  | zero => simp [he0, hR]
  | succ k ih =>
    have hk' : k < n := by omega
    have hprev : |e k| ≤ R := ih (by omega)
    have hbound : -R ≤ e k ∧ e k ≤ R := abs_le.mp hprev
    rcases hstep k hk' with ⟨hpositive, hnegative⟩
    apply abs_le.mpr
    by_cases hsign : 0 ≤ e k
    · rcases hpositive hsign with ⟨hlo, hhi⟩
      constructor <;> linarith
    · have hneg : e k < 0 := lt_of_not_ge hsign
      rcases hnegative hneg with ⟨hlo, hhi⟩
      constructor <;> linarith

/-- A block's endpoint error, within-block increment and deterministic drift
bound give a uniform bound throughout that block. -/
theorem feedback_within_block_bound
    (startValue value driftAtStart driftIncrement R w d : ℝ)
    (hstart : |startValue - driftAtStart| ≤ R)
    (hblock : |value - startValue| ≤ w)
    (hdrift : |driftIncrement| ≤ |d|) :
    |value - (driftAtStart + driftIncrement)| ≤ R + w + |d| := by
  have htriangle := abs_add_le (startValue - driftAtStart)
    ((value - startValue) - driftIncrement)
  have hmiddle := abs_sub_le (value - startValue) 0 driftIncrement
  simp only [sub_zero, zero_sub, abs_neg] at hmiddle
  have hidentity : value - (driftAtStart + driftIncrement) =
      (startValue - driftAtStart) + ((value - startValue) - driftIncrement) := by
    ring
  rw [hidentity]
  linarith

/-- A finite family of block paths satisfying the feedback rule remains in
one fixed tube around a bounded real coordinate. -/
theorem feedback_blockPaths_bound
    {T : Type*} (coordinate : T → ℝ)
    (e : ℕ → ℝ) (block : ℕ → T → ℝ)
    (n : ℕ) (r R w d : ℝ)
    (hR : 0 ≤ R) (hr : 0 ≤ r) (he0 : e 0 = 0)
    (hstep : ∀ k < n,
      (0 ≤ e k → -R ≤ e (k + 1) - e k ∧ e (k + 1) - e k ≤ -r) ∧
      (e k < 0 → r ≤ e (k + 1) - e k ∧ e (k + 1) - e k ≤ R))
    (hblock : ∀ k < n, ∀ t : T, |block k t| ≤ w)
    (hcoordinate : ∀ t, |coordinate t| ≤ 1) :
    ∀ k < n, ∀ t : T,
      |e k + block k t - d * coordinate t| ≤ R + w + |d| := by
  intro k hk t
  have he := feedback_endpoint_error_bound e n r R hR hr he0 hstep k hk.le
  have hd : |d * coordinate t| ≤ |d| := by
    rw [abs_mul]
    calc
      |d| * |coordinate t| ≤ |d| * 1 := by
        exact mul_le_mul_of_nonneg_left (hcoordinate t) (abs_nonneg d)
      _ = |d| := mul_one _
  have h := feedback_within_block_bound (e k)
    (e k + block k t) 0 (d * coordinate t) R w d
    (by simpa using he) (by simpa using hblock k hk t) hd
  simpa only [sub_zero, zero_add] using h

/-- A positive normalized endpoint window still gives a strictly positive
correction after subtracting a drift small relative to the scale. -/
theorem feedback_positive_scaledWindow
    (a r R z d : ℝ) (ha : 0 < a)
    (hz : z / a ∈ Set.Ioo r R) (hd : |d| / a < r / 2) :
    r * a / 2 < z - d ∧ z - d < (R + r / 2) * a := by
  have hzlo : r * a < z := by
    exact (lt_div_iff₀ ha).mp hz.1
  have hzhi : z < R * a := by
    exact (div_lt_iff₀ ha).mp hz.2
  have hdabs : |d| < r * a / 2 := by
    have := (div_lt_iff₀ ha).mp hd
    nlinarith
  constructor <;> nlinarith [neg_abs_le d, le_abs_self d]

/-- The reflected normalized window gives a strictly negative correction
under the same drift bound. -/
theorem feedback_negative_scaledWindow
    (a r R z d : ℝ) (ha : 0 < a)
    (hz : z / a ∈ Set.Ioo (-R) (-r)) (hd : |d| / a < r / 2) :
    -(R + r / 2) * a < z - d ∧ z - d < -(r * a / 2) := by
  have hzlo : -R * a < z := by
    exact (lt_div_iff₀ ha).mp hz.1
  have hzhi : z < -r * a := by
    exact (div_lt_iff₀ ha).mp hz.2
  have hdabs : |d| < r * a / 2 := by
    have := (div_lt_iff₀ ha).mp hd
    nlinarith
  constructor <;> nlinarith [neg_abs_le d, le_abs_self d]

end Real

end

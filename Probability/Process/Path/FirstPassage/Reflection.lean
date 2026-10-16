/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.FirstPassage.Basic
public import Probability.Process.Path.Reflection.Basic

/-!
# First passage under path reflection

The public theorems in this file are:

- `ProbabilityTheory.firstPassageBelow_reflectAfter_eq_of_le`: if the
  first passage below $a$ occurs by $r$, reflecting the path after $r$
  preserves its first-passage time.
- `ProbabilityTheory.firstPassageBelow_le_one_reflectAfter_capped_iff`:
  reflection at the first passage below $a$, capped at time $1$,
  preserves the event of passage by time $1$.
- `ProbabilityTheory.reflectAfter_firstPassageBelow_capped_apply_one`:
  if $f(0)>a$ and passage occurs by $1$, the reflected endpoint is
  $2a-f(1)$.

These pathwise statements support the reflection principle in Theorem 2.1
of S. J. Dilworth and Duncan Wright, *A direct proof of the reflection
principle for Brownian motion*, Theory Stoch. Process. 21(37):2 (2016),
1--3, arXiv:1810.01783.
-/

@[expose] public section

open scoped NNReal

namespace ProbabilityTheory

/-- Reflection after a time already following first passage preserves
the first-passage time. -/
theorem firstPassageBelow_reflectAfter_eq_of_le
    (f : C(ℝ≥0, ℝ)) (a : ℝ) (r : ℝ≥0)
    (h : firstPassageBelow f a ≤ r) :
    firstPassageBelow (reflectAfter f r) a = firstPassageBelow f a := by
  symm
  apply firstPassageBelow_eq_of_agreeOn f (reflectAfter f r) a r
  · intro u hu
    exact (reflectAfter_apply_le f r u hu).symm
  · exact h

/-- Reflection at the first-passage time, capped at time $1$,
preserves the event that passage occurs by time $1$. -/
theorem firstPassageBelow_le_one_reflectAfter_capped_iff
    (f : C(ℝ≥0, ℝ)) (a : ℝ) :
    firstPassageBelow
        (reflectAfter f
          (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA) a ≤ 1 ↔
      firstPassageBelow f a ≤ 1 := by
  by_cases h : firstPassageBelow f a ≤ (1 : WithTop ℝ≥0)
  · obtain ⟨u, _, hu⟩ := (firstPassageBelow_le_iff f a 1).mp h
    have hhit : ∃ t : ℝ≥0, f t ≤ a := ⟨u, hu⟩
    let τ : ℝ≥0 := sInf {t : ℝ≥0 | f t ≤ a}
    have hτ : firstPassageBelow f a = τ := by
      simp only [firstPassageBelow, firstPassageLE, ite_eq_left hhit]
      rfl
    have hτ1 : τ ≤ 1 := by
      rw [hτ] at h
      exact WithTop.coe_le_coe.mp h
    have hcap : (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA = τ := by
      rw [hτ]
      have hmin : min (τ : WithTop ℝ≥0) 1 = τ := min_eq_left (by exact_mod_cast hτ1)
      rw [hmin]
      rfl
    rw [hcap, firstPassageBelow_reflectAfter_eq_of_le f a τ (by rw [hτ])]
  · have hcap : (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA = 1 := by
      rw [min_eq_right (lt_of_not_ge h).le]
      rfl
    rw [hcap]
    exact firstPassageBelow_le_congr_of_agreeOn f (reflectAfter f 1) a 1
      (by intro u hu; exact (reflectAfter_apply_le f 1 u hu).symm) |>.symm

/-- If a path starts above `a` and reaches it by time `1`, reflection
at its first passage sends the endpoint to `2a-f(1)`. -/
theorem reflectAfter_firstPassageBelow_capped_apply_one
    (f : C(ℝ≥0, ℝ)) (a : ℝ) (h0 : a < f 0)
    (h : firstPassageBelow f a ≤ (1 : WithTop ℝ≥0)) :
    reflectAfter f
        (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA 1 =
      2 * a - f 1 := by
  obtain ⟨u, _, hu⟩ := (firstPassageBelow_le_iff f a 1).mp h
  have hhit : ∃ t : ℝ≥0, f t ≤ a := ⟨u, hu⟩
  let τ : ℝ≥0 := sInf {t : ℝ≥0 | f t ≤ a}
  have hτ : firstPassageBelow f a = τ := by
    simp only [firstPassageBelow, firstPassageLE, ite_eq_left hhit]
    rfl
  have hτ1 : τ ≤ 1 := by
    rw [hτ] at h
    exact WithTop.coe_le_coe.mp h
  have hcap : (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA = τ := by
    rw [hτ]
    have hmin : min (τ : WithTop ℝ≥0) 1 = τ := min_eq_left (by exact_mod_cast hτ1)
    rw [hmin]
    rfl
  have hvalue : f τ = a := firstPassageBelow_value_eq f a h0 hhit
  rw [hcap]
  rcases lt_or_eq_of_le hτ1 with hlt | heq
  · rw [reflectAfter_apply_of_lt f τ 1 hlt, hvalue]
  · rw [heq] at hvalue ⊢
    rw [reflectAfter_apply_le f 1 1 le_rfl]
    linarith

end ProbabilityTheory

end

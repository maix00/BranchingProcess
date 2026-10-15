/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.RunningMinimum

/-!
# Minimum of a continuous path on a finite interval

The public definitions and theorems in this file are:

- `ProbabilityTheory.intervalMinimum`:
  $m_f(r,q)=\min_{r\le u\le q}f(u)$ for $r\le q$.
- `ProbabilityTheory.intervalMinimum_le`:
  $m_f(r,q)\le f(u)$ for $r\le u\le q$.
- `ProbabilityTheory.exists_intervalMinimum_eq`:
  some $u\in[r,q]$ attains $m_f(r,q)$.
- `ProbabilityTheory.measurable_intervalMinimum`:
  $f\mapsto m_f(r,q)$ is Borel measurable.

The time-shift representation of the interval minimum supports the
fixed-interval Brownian reflection calculations used in Erwin
Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Ann. Probab. 4(3) (1976), 480--485,
page 484.
-/

@[expose] public section

namespace ProbabilityTheory

open scoped NNReal

/-- Minimum on `[r,q]`, represented through the running minimum of the
path shifted to zero at `r`. -/
noncomputable def intervalMinimum
    (f : C(ℝ≥0, ℝ)) (r q : ℝ≥0) : ℝ :=
  f r + runningMinimum (shiftToZero f r) (q - r)

/-- The interval minimum bounds every value inside the interval. -/
theorem intervalMinimum_le (f : C(ℝ≥0, ℝ))
    {r u q : ℝ≥0} (hru : r ≤ u) (huq : u ≤ q) :
    intervalMinimum f r q ≤ f u := by
  have hu : u - r ≤ q - r := tsub_le_tsub_right huq r
  have hmin := runningMinimum_le (shiftToZero f r) hu
  have hru' : r + (u - r) = u := add_tsub_cancel_of_le hru
  dsimp [intervalMinimum]
  change f r + runningMinimum (shiftToZero f r) (q - r) ≤ f u
  have hbound : runningMinimum (shiftToZero f r) (q - r) ≤
      f u - f r := by
    simpa [shiftToZero, hru'] using hmin
  linarith

/-- The interval minimum is attained by a path value in `[r,q]`. -/
theorem exists_intervalMinimum_eq (f : C(ℝ≥0, ℝ))
    {r q : ℝ≥0} (hrq : r ≤ q) :
    ∃ u : ℝ≥0, r ≤ u ∧ u ≤ q ∧ f u = intervalMinimum f r q := by
  obtain ⟨v, hv, hmin⟩ :=
    exists_runningMinimum_eq (shiftToZero f r) (q - r)
  refine ⟨r + v, le_add_of_nonneg_right (by positivity), ?_, ?_⟩
  · calc
      r + v ≤ r + (q - r) := by
        simpa [add_comm] using add_le_add_left hv.2 r
      _ = q := add_tsub_cancel_of_le hrq
  · dsimp [intervalMinimum]
    rw [← hmin]
    simp [shiftToZero]

/-- Evaluation of a fixed finite-interval minimum is measurable. -/
theorem measurable_intervalMinimum (r q : ℝ≥0) :
    Measurable (fun f : C(ℝ≥0, ℝ) => intervalMinimum f r q) := by
  unfold intervalMinimum
  exact (ContinuousMap.measurable_eval r).add
    ((measurable_runningMinimum (q - r)).comp
      (measurable_shiftToZero.comp
        (measurable_id.prodMk measurable_const)))

end ProbabilityTheory

end

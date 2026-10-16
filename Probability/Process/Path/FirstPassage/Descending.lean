/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.FirstPassage.Basic

/-!
# Descending level hitting times of a continuous path

The public definitions and theorems in this file are:

- `ProbabilityTheory.descendingHittingTime`:
  $\tau_x(f)=\inf\{t\ge0:f(t)\le-x\}$ for $x\ge0$.
- `ProbabilityTheory.descendingHittingTime_mono`:
  $x\le y$ implies $\tau_x(f)\le\tau_y(f)$.
- `ProbabilityTheory.measurable_descendingHittingTime`:
  $f\mapsto\tau_x(f)$ is measurable for each fixed $x$.

For a Brownian path this is the descending hitting-time process
$\{T_{-x}:x\ge0\}$ used in Lemma 2.3, equation (2.2), of Erwin
Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098. Bolthausen cites the Lévy decomposition
in Section 1.7 of K. Itô and H. P. McKean, *Diffusion Processes and
Their Sample Paths*, Springer, 1965, for its jump lengths.
-/

@[expose] public section

open scoped NNReal

namespace ProbabilityTheory

/-- First passage of a continuous path below the level `-x`. -/
noncomputable def descendingHittingTime (f : C(ℝ≥0, ℝ))
    (x : ℝ≥0) : WithTop ℝ≥0 :=
  firstPassageBelow f (-(x : ℝ))

/-- Lower levels are reached no earlier than higher levels. -/
theorem descendingHittingTime_mono (f : C(ℝ≥0, ℝ)) :
    Monotone (descendingHittingTime f) := by
  intro x y hxy
  by_cases hy : descendingHittingTime f y = ⊤
  · simp [hy]
  · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hy
    have hex : ∃ u : ℝ≥0, f u ≤ -(y : ℝ) := by
      by_contra h
      apply hy
      change firstPassageBelow f (-(y : ℝ)) = ⊤
      exact (firstPassageBelow_eq_top_iff f (-(y : ℝ))).2
        (fun u => lt_of_not_ge (fun hu => h ⟨u, hu⟩))
    have hts : sInf {u : ℝ≥0 | f u ≤ -(y : ℝ)} = t := by
      have heq : ((sInf {u : ℝ≥0 | f u ≤ -(y : ℝ)} : ℝ≥0) :
          WithTop ℝ≥0) = t := by
        simpa [descendingHittingTime, firstPassageBelow, firstPassageLE,
          hex] using ht.symm
      exact WithTop.coe_injective heq
    have hpass : f t ≤ -(y : ℝ) := by
      rw [← hts]
      exact firstPassageBelow_attained f (-(y : ℝ)) hex
    have hlevel : -(y : ℝ) ≤ -(x : ℝ) :=
      neg_le_neg (by exact_mod_cast hxy)
    have hxle : descendingHittingTime f x ≤ t :=
      (firstPassageBelow_le_iff f (-(x : ℝ)) t).mpr
        ⟨t, le_rfl, hpass.trans hlevel⟩
    rw [← ht]
    exact hxle

/-- A fixed descending-level hitting time is a measurable function of
the continuous path. -/
theorem measurable_descendingHittingTime (x : ℝ≥0) :
    Measurable (fun f : C(ℝ≥0, ℝ) => descendingHittingTime f x) :=
  measurable_firstPassageBelow (-(x : ℝ))

end ProbabilityTheory

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.AboveStart.FirstWindow.FiniteHorizon

/-!
# First eligible-window time on a finite path space

The public definition and theorems in this file are:

- `ProbabilityTheory.firstWindowTimeFiniteHorizon`:
  the first $t$ with $t+1\le s$ and
  $f(t+u)\ge f(t)$ for every $u\in[0,1]$, or $\infty$ if none exists,
  for $f\in C([0,s],\mathbb R)$.
- `ProbabilityTheory.measurable_firstWindowTimeFiniteHorizon`:
  this map to $[0,\infty]$ is Borel measurable.
- `ProbabilityTheory.firstWindowTimeFiniteHorizon_restrictPathTo`:
  restriction of a whole-time path preserves this first-window time.
- `ProbabilityTheory.firstWindowTimeFiniteHorizon_lt_horizon_iff`:
  the first-window time is finite exactly when it lies below $s$.
- `ProbabilityTheory.continuousAt_firstWindowTimeFiniteHorizon_of_full`:
  continuity of the whole-time functional transfers to the finite
  path space at the restriction of the reference path.

These are the finite-path $T^s$ and restriction $\Pi_s$ in Erwin
Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Lemma 2.4 and Theorem 3.2,
Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The first eligible unit-window time determined by a path on $[0,s]$. -/
noncomputable def firstWindowTimeFiniteHorizon (s : ℝ≥0)
    (f : C(Set.Icc (0 : ℝ≥0) s, ℝ)) : WithTop ℝ≥0 :=
  firstNonnegativeWindowStartUpTo (extendPathConstantAfter s f) s

/-- The first-window time on a finite path space is measurable. -/
theorem measurable_firstWindowTimeFiniteHorizon (s : ℝ≥0) :
    Measurable (firstWindowTimeFiniteHorizon s) :=
  (measurable_firstNonnegativeWindowStartUpTo s).comp
    (continuous_extendPathConstantAfter s).measurable

/-- Whole-time restriction retains the finite-horizon first-window time. -/
theorem firstWindowTimeFiniteHorizon_restrictPathTo
    (f : C(ℝ≥0, ℝ)) (s : ℝ≥0) :
    firstWindowTimeFiniteHorizon s (restrictPathTo s f) =
      firstNonnegativeWindowStartUpTo f s := by
  rw [firstWindowTimeFiniteHorizon,
    extendPathConstantAfter_restrictPathTo,
    firstNonnegativeWindowStartUpTo_freezeAfter]

/-- Every finite eligible start satisfies $t+1\le s$, so the finite
first-window times are separated from the value $\infty$ by $s$. -/
theorem firstWindowTimeFiniteHorizon_lt_horizon_iff
    (s : ℝ≥0) (f : C(Set.Icc (0 : ℝ≥0) s, ℝ)) :
    firstWindowTimeFiniteHorizon s f < (s : WithTop ℝ≥0) ↔
      firstWindowTimeFiniteHorizon s f ≠ ⊤ := by
  constructor
  · intro h
    exact ne_of_lt (h.trans (WithTop.coe_lt_top s))
  · intro h
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp h
    have htime : firstNonnegativeWindowStartUpTo
        (extendPathConstantAfter s f) s = t := ht.symm
    have hbound :=
      (firstNonnegativeWindowStartUpTo_eq_coe_iff
        (extendPathConstantAfter s f) s t).mp htime |>.1
    rw [firstWindowTimeFiniteHorizon, htime]
    have hlt : t < t + 1 :=
      lt_add_of_pos_right t (by norm_num : (0 : ℝ≥0) < 1)
    exact WithTop.coe_lt_coe.mpr (hlt.trans_le hbound)

/-- The horizon itself is never a value of the finite-horizon
first-window-time map. -/
theorem firstWindowTimeFiniteHorizon_ne_horizon
    (s : ℝ≥0) (f : C(Set.Icc (0 : ℝ≥0) s, ℝ)) :
    firstWindowTimeFiniteHorizon s f ≠ (s : WithTop ℝ≥0) := by
  by_cases htop : firstWindowTimeFiniteHorizon s f = ⊤
  · rw [htop]
    exact (WithTop.coe_ne_top : (s : WithTop ℝ≥0) ≠ ⊤).symm
  · exact ne_of_lt ((firstWindowTimeFiniteHorizon_lt_horizon_iff s f).2 htop)

/-- Almost-sure continuity can be transferred from a whole path to
its restriction by extending nearby finite paths with the fixed
reference path's future increments. -/
theorem continuousAt_firstWindowTimeFiniteHorizon_of_full
    (f : C(ℝ≥0, ℝ)) (s : ℝ≥0)
    (hcont : ContinuousAt
      (fun g => firstNonnegativeWindowStartUpTo g s) f) :
    ContinuousAt (firstWindowTimeFiniteHorizon s)
      (restrictPathTo s f) := by
  have hrepresentation (g : C(Set.Icc (0 : ℝ≥0) s, ℝ)) :
      firstWindowTimeFiniteHorizon s g =
        firstNonnegativeWindowStartUpTo (extendPathAlong f s g) s := by
    conv_lhs => rw [← restrictPathTo_extendPathAlong f s g]
    exact firstWindowTimeFiniteHorizon_restrictPathTo
      (extendPathAlong f s g) s
  have hinner : ContinuousAt
      (fun g : C(Set.Icc (0 : ℝ≥0) s, ℝ) =>
        firstNonnegativeWindowStartUpTo (extendPathAlong f s g) s)
      (restrictPathTo s f) := by
    have hcont' : ContinuousAt
        (fun g => firstNonnegativeWindowStartUpTo g s)
        (extendPathAlong f s (restrictPathTo s f)) := by
      simpa only [extendPathAlong_restrictPathTo] using hcont
    exact hcont'.comp (continuous_extendPathAlong f s).continuousAt
  convert hinner using 1
  funext g
  exact hrepresentation g

end ProbabilityTheory

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.DescendingHittingTime
public import Probability.Process.Path.FirstPassageRestart

/-!
# Restart identity for descending hitting times

The public theorem in this file is:

- `ProbabilityTheory.descendingHittingTime_shiftToZero_eq`:
  for finite $\tau_x,\tau_{x+y}$ and $y>0$,
  $\tau_y(f(\tau_x+\cdot)-f(\tau_x))=\tau_{x+y}(f)-\tau_x(f)$,
  provided $f(0)>-x$.

This is the deterministic increment identity for the descending
hitting-time process in the Lévy decomposition invoked by Erwin
Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Lemma 2.3, equation (2.2),
Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open scoped NNReal

namespace ProbabilityTheory

/-- A descending hitting-time increment is the first-passage time of
the path shifted at the first level. -/
theorem descendingHittingTime_shiftToZero_eq
    (f : C(ℝ≥0, ℝ)) (x y : ℝ≥0) (hy : 0 < y)
    (h0 : -(x : ℝ) < f 0) {τx τxy : ℝ≥0}
    (hx : descendingHittingTime f x = τx)
    (hxy : descendingHittingTime f (x + y) = τxy) :
    descendingHittingTime (shiftToZero f τx) y =
      ((τxy - τx : ℝ≥0) : WithTop ℝ≥0) := by
  have hba : -((x + y : ℝ≥0) : ℝ) < -(x : ℝ) := by
    have hy' : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
    simp only [NNReal.coe_add]
    linarith
  have hrestart := firstPassageBelow_shiftToZero_eq f hba h0 hx hxy
  change firstPassageBelow (shiftToZero f τx) (-(y : ℝ)) =
    ((τxy - τx : ℝ≥0) : WithTop ℝ≥0)
  convert hrestart using 1
  simp [NNReal.coe_add]

end ProbabilityTheory

end

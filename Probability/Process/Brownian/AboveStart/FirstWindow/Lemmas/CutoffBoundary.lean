/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Probability.BrownianMotion.Basic
import Probability.Process.Brownian.PathLaw.ContinuousPathLaw
import Probability.Process.Path.AboveStart.FirstWindow.Time.Continuity
import Probability.Process.Path.AboveStart.FirstWindow.Time.RunningMinimum
import Probability.Process.Brownian.Reflection.Path.AboveRunningMinimum

/-!
# The finite-horizon first-window boundary event

## Internal proof declarations

The proof-support lemma in this file is:

- `ProbabilityTheory.IsBrownianReal.measure_firstNonnegativeWindowStartUpTo_eq_last`:
  for $s>1$, the probability that $T^s=s-1$ is zero.

This is the fixed-time non-atom step in equation (2.3) of Lemma 2.3 in
Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks
Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098.
-/

section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- Bolthausen's Lemma 2.3, equation (2.3): the first unit window
cannot start at the last admissible time with positive probability. -/
lemma IsBrownianReal.measure_firstNonnegativeWindowStartUpTo_eq_last
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u))
    {s : ℝ≥0} (hs : 1 < s) :
    P {ω | firstNonnegativeWindowStartUpTo
      (hB.continuousPathMap hBmeasurable ω) s = s - 1} = 0 := by
  let t : ℝ≥0 := s - 1
  have ht : 0 < t := tsub_pos_iff_lt.mpr hs
  have hts : t + 1 = s := by
    dsimp [t]
    exact tsub_add_cancel_of_le hs.le
  have hAE : ∀ᵐ ω ∂P, firstNonnegativeWindowStartUpTo
      (hB.continuousPathMap hBmeasurable ω) s ≠ s - 1 := by
    filter_upwards [hB.ae_aboveRunningMinimum_pos hBmeasurable ht]
      with ω hpos hfirst
    have hfirst' : firstNonnegativeWindowStartUpTo
        (hB.continuousPathMap hBmeasurable ω) (t + 1) = t := by
      simpa [hts, t] using hfirst
    have hzero : aboveRunningMinimum
        (hB.continuousPathMap hBmeasurable ω) t = 0 := by
      rw [aboveRunningMinimum_eq_zero_iff]
      exact (firstNonnegativeWindowStartUpTo_runningMinimum
        (hB.continuousPathMap hBmeasurable ω) (t + 1) t hfirst').1
    exact (ne_of_gt hpos) hzero
  simpa only [not_not] using (ae_iff).mp hAE

end ProbabilityTheory

end

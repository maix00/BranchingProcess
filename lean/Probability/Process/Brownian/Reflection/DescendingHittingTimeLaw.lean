/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Reflection.FirstPassagePrinciple
public import Probability.Process.Path.FirstPassage.Descending

/-!
# One-dimensional law of descending Brownian hitting times

The public theorems in this file are:

- `ProbabilityTheory.IsBrownianReal.measure_descendingHittingTime_le`:
  for $x,t>0$, $\mathbb P(\tau_x\le t)=2\mathbb P(B_t<-x)$,
  where $\tau_x=\inf\{u:B_u\le-x\}$.
- `ProbabilityTheory.IsBrownianReal.measure_descendingHittingTime_eq_zero`:
  the first-passage time of a positive level has no atom at any fixed
  positive time.

This is the reflection-principle marginal of the descending first-passage
process whose Lévy decomposition is cited in Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Lemma 2.3, equation (2.2), Ann. Probab. 4(3) (1976),
480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The fixed-level Brownian hitting-time distribution, directly from
the reflection principle for the running minimum. -/
theorem IsBrownianReal.measure_descendingHittingTime_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u))
    {t x : ℝ≥0} (ht : 0 < t) (hx : 0 < x) :
    let μ := P.map (hB.continuousPathMap hBmeasurable)
    μ {f : C(ℝ≥0, ℝ) | descendingHittingTime f x ≤ t} =
      2 * μ {f : C(ℝ≥0, ℝ) | f t < -(x : ℝ)} := by
  simpa only [descendingHittingTime, ← runningMinimum_le_iff_firstPassageBelow_le]
    using hB.measure_runningMinimum_le hBmeasurable ht
      (show -(x : ℝ) < 0 by exact neg_lt_zero.mpr (by exact_mod_cast hx))

/-- A Brownian descending hitting time has no atom at a positive time.
At first passage the running minimum equals the passage level, and the
reflection principle gives an atomless running minimum. -/
theorem IsBrownianReal.measure_descendingHittingTime_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u))
    {t x : ℝ≥0} (ht : 0 < t) (_hx : 0 < x) :
    let μ := P.map (hB.continuousPathMap hBmeasurable)
    μ {f : C(ℝ≥0, ℝ) | descendingHittingTime f x = t} = 0 := by
  dsimp
  let μ := P.map (hB.continuousPathMap hBmeasurable)
  have hsubset :
      {f : C(ℝ≥0, ℝ) | descendingHittingTime f x = t} ⊆
        {f | runningMinimum f t = -(x : ℝ)} := by
    intro f hf
    exact runningMinimum_eq_of_firstPassageBelow_eq f (-(x : ℝ)) ht hf
  exact measure_mono_null hsubset
    (hB.measure_runningMinimum_eq hBmeasurable ht (-(x : ℝ)))

end ProbabilityTheory

end

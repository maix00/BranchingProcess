/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Reflection.FirstPassagePrinciple
public import Probability.Process.Brownian.TimeReversal.FiniteHorizon
public import Probability.Process.Path.AboveStart.RunningMinimum

/-!
# Brownian height above its running minimum

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.ae_aboveRunningMinimum_pos`:
  for every fixed $t>0$, $W(t)-\min_{0\le u\le t}W(u)>0$ almost surely.
- `ProbabilityTheory.IsBrownianReal.measure_firstNonnegativeWindowStartUpTo_eq_last`:
  for $s>1$, the probability that $T^s=s-1$ is zero.

This is the fixed-time non-atom step in equation (2.3) of Lemma 2.3 in
Erwin Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098. The proof uses the Brownian time reversal
and reflection principle underlying the Lévy identity cited there.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- At a fixed positive time a Brownian path is strictly above its
running minimum almost surely. -/
theorem IsBrownianReal.ae_aboveRunningMinimum_pos
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u))
    {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ ω ∂P, 0 < aboveRunningMinimum
      (hB.continuousPathMap hBmeasurable ω) t := by
  let R := reverseBrownianBefore B t
  have hR : IsBrownianReal R P := hB.reverseBrownianBefore_isBrownianReal t
  have hRmeas (u : ℝ≥0) : Measurable (R u) :=
    measurable_reverseBrownianBefore hBmeasurable t u
  let N : ℝ≥0 → Ω → ℝ := fun u ω => -R u ω
  have hN : IsBrownianReal N P := hR.neg
  have hNmeas (u : ℝ≥0) : Measurable (N u) := (hRmeas u).neg
  let pathN := hN.continuousPathMap hNmeas
  let pathB := hB.continuousPathMap hBmeasurable
  letI : IsProbabilityMeasure P :=
    (hB.toIsPreBrownianReal.hasLaw ∅).isProbabilityMeasure
  have hset : MeasurableSet {f : C(ℝ≥0, ℝ) | runningMinimum f t < 0} :=
    measurableSet_runningMinimum_lt_zero t
  have hprob : (P.map pathN) {f : C(ℝ≥0, ℝ) | runningMinimum f t < 0} = 1 :=
    hN.measure_runningMinimum_lt_zero hNmeas ht
  have hpathNeg : ∀ᵐ ω ∂P, runningMinimum (pathN ω) t < 0 := by
    have hμ : ∀ᵐ f ∂(P.map pathN), runningMinimum f t < 0 :=
      (mem_ae_iff_prob_eq_one hset).2 hprob
    exact (ae_map_iff (hN.measurable_continuousPathMap hNmeas).aemeasurable
      hset).1 hμ
  filter_upwards [hpathNeg, hN.continuousPathMap_ae_eq hNmeas,
    hB.continuousPathMap_ae_eq hBmeasurable] with ω hmin hpathN hpathB
  obtain ⟨u, hu, hvalue⟩ := exists_runningMinimum_eq (pathN ω) t
  have hRpos : 0 < R u ω := by
    have hneg : pathN ω u < 0 := by rw [hvalue]; exact hmin
    rw [hpathN u] at hneg
    dsimp [N] at hneg
    linarith
  have hBu : runningMinimum (pathB ω) t ≤ B (t - u) ω := by
    have hle : t - u ≤ t := tsub_le_self
    rw [← hpathB (t - u)]
    exact runningMinimum_le (pathB ω) hle
  have hRformula : R u ω = B t ω - B (t - u) ω := by
    simp [R, reverseBrownianBefore, hu.2]
  change 0 < pathB ω t - runningMinimum (pathB ω) t
  rw [hpathB t]
  linarith

/-- Bolthausen's Lemma 2.3, equation (2.3): the first unit window
cannot start at the last admissible time with positive probability. -/
theorem IsBrownianReal.measure_firstNonnegativeWindowStartUpTo_eq_last
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
    have hzero := firstNonnegativeWindowStartUpTo_lastStart_aboveRunningMinimum_eq_zero
      (hB.continuousPathMap hBmeasurable ω) t hfirst'
    exact (ne_of_gt hpos) hzero
  simpa only [not_not] using (ae_iff).mp hAE

end ProbabilityTheory

end

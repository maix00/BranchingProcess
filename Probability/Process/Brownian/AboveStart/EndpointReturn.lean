/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.AboveStart.InteriorReturn
public import Probability.Process.Brownian.Reflection.Path.UnboundedBelow

/-!
# Endpoint returns and descending Brownian hitting times

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.ae_endpointReturn_hittingTimeRightLimit`:
  almost surely, if the first qualifying unit window starts at $t$ and
  returns to its starting level $-x$ at $t+1$, then $\tau_x=t$,
  $t+1<\tau_y$ for every $y>x$, and for every $v>t+1$ there is
  $y>x$ with $\tau_y\le v$.

This is the pathwise identification of the unit-length jump used in
equation (2.2) of Lemma 2.3 in Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann.
Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
The separate probabilistic assertion that the hitting-time process has
no jump of this length comes from the Lévy decomposition cited there.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- Outside the Brownian-null three-contact event, an endpoint return
creates an exact unit jump of the descending hitting-time process in
the sense of its two one-sided level limits. -/
theorem IsBrownianReal.ae_endpointReturn_hittingTimeRightLimit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) :
    ∀ᵐ ω ∂P, ∀ s t x : ℝ≥0,
      firstNonnegativeWindowStartUpTo
          (hB.continuousPathMap hBmeasurable ω) s = t →
      hB.continuousPathMap hBmeasurable ω (t + 1) =
        hB.continuousPathMap hBmeasurable ω t →
      hB.continuousPathMap hBmeasurable ω t = -(x : ℝ) →
      descendingHittingTime
          (hB.continuousPathMap hBmeasurable ω) x = t ∧
        (∀ y : ℝ≥0, x < y →
          (t + 1 : WithTop ℝ≥0) <
            descendingHittingTime
              (hB.continuousPathMap hBmeasurable ω) y) ∧
        (∀ v : ℝ≥0, t + 1 < v →
          ∃ y : ℝ≥0, x < y ∧
            descendingHittingTime
              (hB.continuousPathMap hBmeasurable ω) y ≤ v) := by
  let pathB := hB.continuousPathMap hBmeasurable
  have hno : ∀ᵐ ω ∂P, ¬ HasTripleRunningMinimumContact (pathB ω) := by
    apply ae_iff.mpr
    simpa [pathB] using
      hB.measure_tripleRunningMinimumContact_eq_zero hBmeasurable
  have hdesc : ∀ᵐ ω ∂P,
      ∀ a : ℝ, ∃ u : ℝ≥0, pathB ω u < a := by
    exact ae_of_ae_map
      (hB.measurable_continuousPathMap hBmeasurable).aemeasurable
      (hB.ae_continuousPath_unboundedBelow hBmeasurable)
  filter_upwards [hno, hdesc] with ω hω hωdesc s t x hfirst hend hlevel
  have hgap :=
    firstNonnegativeWindowStartUpTo_endpointReturn_descendingHittingTime
      (pathB ω) s t x hfirst hend hlevel hω
  refine ⟨hgap.1, hgap.2, ?_⟩
  intro v hvt
  exact firstNonnegativeWindowStartUpTo_endpointReturn_hittingTimeRightLimit
    (pathB ω) s t x hfirst hend hlevel hω (hωdesc (pathB ω t)) v hvt

end ProbabilityTheory

end

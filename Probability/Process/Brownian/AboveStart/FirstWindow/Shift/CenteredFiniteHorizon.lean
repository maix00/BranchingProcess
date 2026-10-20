/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.AboveStart.FirstWindow.CenteredFiniteHorizon
public import Probability.Process.Brownian.AboveStart.FirstWindow.Shift.Centered

/-!
# Brownian continuity of finite-horizon centered first-window paths

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.ae_continuousAt_centeredFirstWindowShiftFiniteHorizon`:
  for every finite $s$, the centered map
  $C([0,s],\mathbb R)\to C([0,1],\mathbb R)$ is continuous
  $P^s$-almost everywhere.

This is the centered counterpart of the continuity step in
Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Lemma 2.5 and Theorem 3.2,
Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The centered first-window map is almost surely continuous under
the Brownian law projected to a finite time interval. -/
theorem IsBrownianReal.ae_continuousAt_centeredFirstWindowShiftFiniteHorizon
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) (s : ℝ≥0) :
    ∀ᵐ f ∂finiteHorizonPathLaw
      (P.map (hB.continuousPathMap hBmeasurable)) s,
      ContinuousAt (centeredFirstWindowShiftFiniteHorizon s) f := by
  let pathB := hB.continuousPathMap hBmeasurable
  have hmeas : MeasurableSet
      {f : C(Set.Icc (0 : ℝ≥0) s, ℝ) |
        ContinuousAt (centeredFirstWindowShiftFiniteHorizon s) f} :=
    measurableSet_of_continuousAt _
  rw [finiteHorizonPathLaw, Measure.map_map]
  · apply (ae_map_iff
      (((continuous_restrictPathTo s).measurable.comp
        (hB.measurable_continuousPathMap hBmeasurable)).aemeasurable)
      hmeas).2
    filter_upwards [hB.ae_continuousAt_centeredFirstWindowShiftUpTo
      hBmeasurable s] with ω hω
    exact continuousAt_centeredFirstWindowShiftFiniteHorizon_of_full
      (pathB ω) s hω
  · exact (continuous_restrictPathTo s).measurable
  · exact hB.measurable_continuousPathMap hBmeasurable

end ProbabilityTheory

end

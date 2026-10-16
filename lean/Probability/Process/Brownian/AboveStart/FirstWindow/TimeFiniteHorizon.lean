/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.AboveStart.FirstWindow.TimeFiniteHorizon
public import Probability.Process.Brownian.AboveStart.FirstWindow.Continuity
import Mathlib.Topology.Metrizable.Real

/-!
# Brownian continuity of finite-horizon first-window times

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.ae_continuousAt_firstWindowTimeFiniteHorizon`:
  for every finite $s$, the first eligible-window time on
  $C([0,s],\mathbb R)$ is continuous almost everywhere under the
  projected Brownian path law $P^s$.

This is the finite-path form of Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Lemma 2.4, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- Bolthausen's almost-sure continuity statement for $T^s$ under $P^s$. -/
theorem IsBrownianReal.ae_continuousAt_firstWindowTimeFiniteHorizon
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) (s : ℝ≥0) :
    ∀ᵐ f ∂finiteHorizonPathLaw
      (P.map (hB.continuousPathMap hBmeasurable)) s,
      ContinuousAt (firstWindowTimeFiniteHorizon s) f := by
  let pathB := hB.continuousPathMap hBmeasurable
  have hmeas : MeasurableSet
      {f : C(Set.Icc (0 : ℝ≥0) s, ℝ) |
        ContinuousAt (firstWindowTimeFiniteHorizon s) f} :=
    (IsGδ.setOfPred_continuousAt _).measurableSet
  rw [finiteHorizonPathLaw, Measure.map_map]
  · apply (ae_map_iff
      (((continuous_restrictPathTo s).measurable.comp
        (hB.measurable_continuousPathMap hBmeasurable)).aemeasurable)
      hmeas).2
    filter_upwards [hB.ae_continuousAt_firstNonnegativeWindowStartUpTo
      hBmeasurable s] with ω hω
    exact continuousAt_firstWindowTimeFiniteHorizon_of_full
      (pathB ω) s hω
  · exact (continuous_restrictPathTo s).measurable
  · exact hB.measurable_continuousPathMap hBmeasurable

end ProbabilityTheory

end

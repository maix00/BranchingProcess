/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.AboveStart.FirstWindowFiniteHorizon
public import Probability.Process.Brownian.AboveStart.FirstWindowShift

/-!
# Finite-horizon Brownian first-window law

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.ae_continuousAt_firstWindowShiftFiniteHorizon`:
  for every finite $s$, the map
  $\Phi_s:C([0,s],\mathbb R)\to C([0,1],\mathbb R)$ is continuous
  $P^s$-almost everywhere, where $P^s=P\circ\Pi_s^{-1}$ is the
  Brownian path law projected to $[0,s]$.

This is the path-space and measure-theoretic formulation of
Erwin Bolthausen, *On a functional central limit theorem for random
walks conditioned to stay positive*, Lemma 2.5, Ann. Probab. 4(3)
(1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- Bolthausen's finite-horizon map is almost surely continuous under
the projected Brownian law $P^s$. -/
theorem IsBrownianReal.ae_continuousAt_firstWindowShiftFiniteHorizon
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) (s : ℝ≥0) :
    ∀ᵐ f ∂finiteHorizonPathLaw
      (P.map (hB.continuousPathMap hBmeasurable)) s,
      ContinuousAt (firstWindowShiftFiniteHorizon s) f := by
  let pathB := hB.continuousPathMap hBmeasurable
  have hmeas : MeasurableSet
      {f : C(Set.Icc (0 : ℝ≥0) s, ℝ) |
        ContinuousAt (firstWindowShiftFiniteHorizon s) f} :=
    measurableSet_of_continuousAt _
  rw [finiteHorizonPathLaw, Measure.map_map]
  · apply (ae_map_iff
      (((continuous_restrictPathTo s).measurable.comp
        (hB.measurable_continuousPathMap hBmeasurable)).aemeasurable)
      hmeas).2
    filter_upwards [hB.ae_continuousAt_shiftAtFirstNonnegativeWindowStartUpTo
      hBmeasurable s] with ω hω
    exact continuousAt_firstWindowShiftFiniteHorizon_of_full
      (pathB ω) s hω
  · exact (continuous_restrictPathTo s).measurable
  · exact hB.measurable_continuousPathMap hBmeasurable

end ProbabilityTheory

end

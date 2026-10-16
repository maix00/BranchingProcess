/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.FiniteHorizonScaling
public import Probability.Process.Brownian.ContinuousModification
public import Probability.Distributions.Stable.Gaussian
public import Topology.ContinuousMap.LastZero
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# The last zero of Brownian motion before time one

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.ae_lastZero_restrictPathToUnitInterval_lt_top`:
  for Brownian motion $B$ started at zero and
  $g=\sup\{t\in[0,1]:B_t=0\}$, one has $g<1$ almost surely.
- `ProbabilityTheory.IsBrownianReal.ae_lastZeroMeanderTransform_positive`:
  the transformed Brownian path starts at zero and is strictly
  positive at every time $t\in(0,1]$ almost surely.

This verifies that the normalization $(1-g)^{-1/2}$ in Donald L.
Iglehart, *Functional Central Limit Theorems for Random Walks Conditioned
to Stay Positive*, Ann. Probab. 2(4) (1974), 608--619, DOI 10.1214/aop/1176996607, Section 3,
is defined almost surely.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The terminal excursion before time one has positive duration almost
surely because the Brownian endpoint has a nonatomic Gaussian law. -/
theorem IsBrownianReal.ae_lastZero_restrictPathToUnitInterval_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) :
    ∀ᵐ ω ∂P,
      ContinuousMap.lastZero
        (restrictPathToUnitInterval
          (hB.continuousPathMap hmeasurable ω)) < ⊤ := by
  have hone : ∀ᵐ ω ∂P, B 1 ω ≠ 0 := by
    exact (hB.hasLaw_eval 1).ae_iff
      (measurableSet_setOfPred.1 (by
        convert (measurableSet_singleton (0 : ℝ)).compl using 1
        ext x
        simp)) |>.2
      (@Measure.ae_ne ℝ _ (gaussianReal 0 1)
        (nullSingletonClass_gaussianReal (by norm_num)) 0)
  filter_upwards [hB.continuousPathMap_ae_eq hmeasurable,
    hB.eval_zero_ae_eq_zero, hone] with ω hpath hzero hone
  apply ContinuousMap.lastZero_lt_top_of_ne_zero
  · change hB.continuousPathMap hmeasurable ω 0 = 0
    rw [hpath]
    exact hzero
  · change hB.continuousPathMap hmeasurable ω 1 ≠ 0
    rw [hpath]
    exact hone

/-- Iglehart's terminal-excursion transform starts at zero and stays
strictly positive at every later time almost surely. -/
theorem IsBrownianReal.ae_lastZeroMeanderTransform_positive
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) :
    ∀ᵐ ω ∂P,
      let path := restrictPathToUnitInterval
        (hB.continuousPathMap hmeasurable ω)
      ContinuousMap.lastZeroMeanderTransform path 0 = 0 ∧
        ∀ t : unitInterval, 0 < t →
          0 < ContinuousMap.lastZeroMeanderTransform path t := by
  filter_upwards [hB.continuousPathMap_ae_eq hmeasurable,
    hB.eval_zero_ae_eq_zero,
    hB.ae_lastZero_restrictPathToUnitInterval_lt_top hmeasurable]
    with ω hpath hzero hcut
  dsimp only
  constructor
  · apply ContinuousMap.lastZeroMeanderTransform_zero
    change hB.continuousPathMap hmeasurable ω 0 = 0
    rw [hpath]
    exact hzero
  · intro t ht
    exact ContinuousMap.lastZeroMeanderTransform_pos_of_lastZero_lt_top
      _ hcut ht

end ProbabilityTheory

end

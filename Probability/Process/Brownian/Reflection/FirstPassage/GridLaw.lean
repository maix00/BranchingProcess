/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Reflection.FirstPassage.FiniteStoppingTime
public import Probability.Process.Path.FirstPassage.GridApproximation
import MeasureTheory.Measure.Convergence.MapInvariance

/-!
# Brownian reflection at first-passage grid times

The public theorems in this file are:

- `ProbabilityTheory.IsBrownianReal.measure_reflectAfter_firstPassageGridCeiling_eq`:
  reflection at the first grid time after continuous passage below $a$
  preserves Brownian path law.
- `ProbabilityTheory.IsBrownianReal.measure_reflectAfter_firstPassageBeforeOne_eq`:
  reflection at the first passage below $a$, capped at $1$, preserves
  Brownian path law.

The finite-valued stopping-time argument and its grid approximation formalize
Theorem 2.1 of S. J. Dilworth and Duncan Wright, *A direct proof of the
reflection principle for Brownian motion*, Theory Stoch. Process.
21(37):2 (2016), 1--3, arXiv:1810.01783. The resulting reflection principle
supports the Lévy running-minimum identity in Lemma 2.3, equation (2.2), of
Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks
Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal Classical

namespace ProbabilityTheory

/-- Reflection at the first grid time after continuous first passage
preserves Brownian path law. This is the finite-valued stopping-time
approximation in Theorem 2.1 of S. J. Dilworth and Duncan Wright,
*A direct proof of the reflection principle for Brownian motion*,
arXiv:1810.01783. -/
theorem IsBrownianReal.measure_reflectAfter_firstPassageGridCeiling_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t))
    (N : ℕ) (r : Fin (N + 1) → ℝ≥0) (hr : Monotone r)
    (a : ℝ) :
    (P.map (hB.continuousPathMap hBmeasurable)).map
        (fun f => reflectAfter f (r (firstPassageGridCeiling N r a f))) =
      P.map (hB.continuousPathMap hBmeasurable) := by
  have hT : Measurable (firstPassageGridCeiling N r a) :=
    measurable_firstPassageGridCeiling N r a
  have hlocal (i : Fin (N + 1)) (f g : C(ℝ≥0, ℝ))
      (hprefix : ∀ v : ℝ≥0, v ≤ r i → f v = g v) :
      firstPassageGridCeiling N r a f = i ↔
        firstPassageGridCeiling N r a g = i :=
    firstPassageGridCeiling_eq_iff_of_agreeOn N r hr a i f g hprefix
  exact hB.measure_reflectAfter_finitePathwiseStoppingTime_eq
    hBmeasurable (firstPassageGridCeiling N r a) r hT hlocal

/-- Reflection at the first passage below `a`, capped at time `1`,
preserves Brownian path law. Finite-grid reflection invariance passes to
the pointwise path limit by bounded convergence, as in Theorem 2.1 of
S. J. Dilworth and Duncan Wright, *A direct proof of the reflection
principle for Brownian motion*, arXiv:1810.01783. -/
theorem IsBrownianReal.measure_reflectAfter_firstPassageBeforeOne_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t)) (a : ℝ) :
    (P.map (hB.continuousPathMap hBmeasurable)).map
        (fun f => reflectAfter f
          (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA) =
      P.map (hB.continuousPathMap hBmeasurable) := by
  let μ := P.map (hB.continuousPathMap hBmeasurable)
  haveI : IsProbabilityMeasure P := (hB.hasLaw ∅).isProbabilityMeasure
  haveI : IsFiniteMeasure μ := inferInstance
  let F : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ) := fun f =>
    reflectAfter f (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA
  let Fₙ : ℕ → C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ) := fun n f =>
    reflectAfter f (unitIntervalGridTime n
      (firstPassageGridCeiling (n + 1) (unitIntervalGridTime n) a f))
  have hTmeas : Measurable
      (fun f : C(ℝ≥0, ℝ) =>
        (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA) :=
    ((measurable_firstPassageBelow a).min measurable_const).untopA
  have hF : Measurable F :=
    measurable_reflectAfter_pair.comp (measurable_id.prodMk hTmeas)
  have hFₙ (n : ℕ) : Measurable (Fₙ n) := by
    have hT : Measurable (fun f : C(ℝ≥0, ℝ) =>
        unitIntervalGridTime n
          (firstPassageGridCeiling (n + 1) (unitIntervalGridTime n) a f)) :=
      (measurable_of_finite (unitIntervalGridTime n)).comp
        (measurable_firstPassageGridCeiling (n + 1) (unitIntervalGridTime n) a)
    exact measurable_reflectAfter_pair.comp (measurable_id.prodMk hT)
  have hlim (f : C(ℝ≥0, ℝ)) :
      Filter.Tendsto (fun n => Fₙ n f) Filter.atTop (nhds (F f)) :=
    tendsto_reflectAfter_unitIntervalGridCeiling_capped a f
  have hinv (n : ℕ) : μ.map (Fₙ n) = μ :=
    hB.measure_reflectAfter_firstPassageGridCeiling_eq hBmeasurable
      (n + 1) (unitIntervalGridTime n) (unitIntervalGridTime_mono n) a
  exact Measure.map_eq_of_pointwise_limit μ F Fₙ hF hFₙ hlim hinv


end ProbabilityTheory

end

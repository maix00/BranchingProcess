/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Independence.FiniteStoppingTime
public import Probability.Process.Brownian.Independence.StoppedPast
public import Probability.Process.Path.FirstPassage.GridApproximation
import Probability.MeasureTheory.Convergence.InvariantLaw

/-!
# Brownian future at a first-passage observation grid

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.measure_shiftToZero_firstPassageGridCeiling_eq`:
  for a finite monotone observation grid, the Brownian future increment
  path at the first grid time after passage below a fixed level has the
  original Brownian path law.
- `ProbabilityTheory.IsBrownianReal.indepFun_shiftToZero_freezeAfter_firstPassageGridCeiling`:
  at the same finite grid time, the future increment path is independent
  of the stopped past.
- `ProbabilityTheory.IsBrownianReal.measure_shiftToZero_firstPassageBeforeOne_eq`:
  the same path-law identity at the first passage time capped at $1$.

This is the grid approximation to the strong Markov step behind the
Lévy decomposition cited in Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*,
Lemma 2.3, equation (2.2), Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098, referring to Kiyosi Itô and Henry P.
McKean, *Diffusion Processes and Their Sample Paths* (1965), §1.7.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- First-passage observation times are finite-valued pathwise stopping
times, so their shifted future paths have Brownian law. -/
theorem IsBrownianReal.measure_shiftToZero_firstPassageGridCeiling_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u))
    (N : ℕ) (r : Fin (N + 1) → ℝ≥0) (hr : Monotone r)
    (a : ℝ) :
    P.map (fun ω =>
      shiftToZero (hB.continuousPathMap hBmeasurable ω)
        (r (firstPassageGridCeiling N r a
          (hB.continuousPathMap hBmeasurable ω)))) =
      P.map (hB.continuousPathMap hBmeasurable) := by
  exact hB.measure_shiftToZero_finitePathwiseStoppingTime_eq
    hBmeasurable (firstPassageGridCeiling N r a) r
    (measurable_firstPassageGridCeiling N r a)
    (fun i f g hprefix =>
      firstPassageGridCeiling_eq_iff_of_agreeOn
        N r hr a i f g hprefix)

/-- On a finite first-passage observation grid, the future increment
path and the stopped past path are independent. -/
theorem IsBrownianReal.indepFun_shiftToZero_freezeAfter_firstPassageGridCeiling
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u))
    (N : ℕ) (r : Fin (N + 1) → ℝ≥0) (hr : Monotone r)
    (a : ℝ) :
    (fun ω => shiftToZero (hB.continuousPathMap hBmeasurable ω)
      (r (firstPassageGridCeiling N r a
        (hB.continuousPathMap hBmeasurable ω)))) ⟂ᵢ[P]
    (fun ω => freezeAfter (hB.continuousPathMap hBmeasurable ω)
      (r (firstPassageGridCeiling N r a
        (hB.continuousPathMap hBmeasurable ω)))) := by
  exact hB.indepFun_shiftToZero_freezeAfter_finitePathwiseStoppingTime
    hBmeasurable (firstPassageGridCeiling N r a) r
    (measurable_firstPassageGridCeiling N r a)
    (fun i f g hprefix =>
      firstPassageGridCeiling_eq_iff_of_agreeOn
        N r hr a i f g hprefix)

/-- Grid approximation and continuity of the path shift yield the
Brownian future-path law at a bounded first-passage stopping time. -/
theorem IsBrownianReal.measure_shiftToZero_firstPassageBeforeOne_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) (a : ℝ) :
    (P.map (hB.continuousPathMap hBmeasurable)).map
        (fun f => shiftToZero f
          (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA) =
      P.map (hB.continuousPathMap hBmeasurable) := by
  let μ := P.map (hB.continuousPathMap hBmeasurable)
  haveI : IsProbabilityMeasure P := (hB.hasLaw ∅).isProbabilityMeasure
  haveI : IsFiniteMeasure μ := inferInstance
  let F : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ) := fun f =>
    shiftToZero f (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA
  let Fₙ : ℕ → C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ) := fun n f =>
    shiftToZero f (unitIntervalGridTime n
      (firstPassageGridCeiling (n + 1) (unitIntervalGridTime n) a f))
  have hTmeas : Measurable
      (fun f : C(ℝ≥0, ℝ) =>
        (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA) :=
    ((measurable_firstPassageBelow a).min measurable_const).untopA
  have hF : Measurable F :=
    measurable_shiftToZero.comp (measurable_id.prodMk hTmeas)
  have hFₙ (n : ℕ) : Measurable (Fₙ n) := by
    have hT : Measurable (fun f : C(ℝ≥0, ℝ) =>
        unitIntervalGridTime n
          (firstPassageGridCeiling (n + 1) (unitIntervalGridTime n) a f)) :=
      (measurable_of_finite (unitIntervalGridTime n)).comp
        (measurable_firstPassageGridCeiling (n + 1) (unitIntervalGridTime n) a)
    exact measurable_shiftToZero.comp (measurable_id.prodMk hT)
  have hlim (f : C(ℝ≥0, ℝ)) :
      Filter.Tendsto (fun n => Fₙ n f) Filter.atTop (nhds (F f)) := by
    have htime := tendsto_unitIntervalGridCeiling_time_capped a f
    exact continuous_shiftToZero.continuousAt.tendsto.comp
      (tendsto_const_nhds.prodMk_nhds htime)
  have hinv (n : ℕ) : μ.map (Fₙ n) = μ := by
    rw [Measure.map_map (hFₙ n)
      (hB.measurable_continuousPathMap hBmeasurable)]
    exact hB.measure_shiftToZero_firstPassageGridCeiling_eq hBmeasurable
      (n + 1) (unitIntervalGridTime n) (unitIntervalGridTime_mono n) a
  exact Measure.map_eq_of_pointwise_limit μ F Fₙ hF hFₙ hlim hinv

end ProbabilityTheory

end

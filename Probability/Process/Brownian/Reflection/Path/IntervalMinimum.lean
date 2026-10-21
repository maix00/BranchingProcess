/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Extrema.IntervalMinimum
public import Probability.Process.Brownian.Independence.PastFuturePaths

/-!
# Atomlessness of a Brownian interval minimum

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.measure_intervalMinimum_eq`:
  for $r<q$ and $a\in\mathbb R$,
  $\mathbb P(\min_{r\le t\le q}B_t=a)=0$.
- `ProbabilityTheory.IsBrownianReal.measure_negIntervalMinimum_eq`:
  $\mathbb P(\min_{r\le t\le q}(-B_t)=a)=0$ for $r<q$.

The proof combines independence of the path before and after a fixed
time with the atomless running-minimum law from the Brownian reflection
principle. This is the fixed-interval regularity needed to compare the
last sign change and last zero in the sketch following Theorem 3.2 of
Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976),
480--485, DOI 10.1214/aop/1176996098, page 484.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The minimum on any nondegenerate deterministic Brownian interval
has an atomless law. -/
theorem IsBrownianReal.measure_intervalMinimum_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t))
    {r q : ℝ≥0} (hrq : r < q) (a : ℝ) :
    let μ := P.map (hB.continuousPathMap hmeasurable)
    μ {f : C(ℝ≥0, ℝ) | intervalMinimum f r q = a} = 0 := by
  dsimp
  let pathB := hB.continuousPathMap hmeasurable
  let future : Ω → C(ℝ≥0, ℝ) := fun ω => shiftToZero (pathB ω) r
  let X : Ω → ℝ := fun ω => a - pathB ω r
  let Y : Ω → ℝ := fun ω => runningMinimum (future ω) (q - r)
  have hpath : Measurable pathB :=
    hB.measurable_continuousPathMap hmeasurable
  have hfuture : Measurable future :=
    measurable_shiftToZero.comp (hpath.prodMk measurable_const)
  have hX : Measurable X :=
    measurable_const.sub ((ContinuousMap.measurable_eval r).comp hpath)
  have hY : Measurable Y :=
    (measurable_runningMinimum (q - r)).comp hfuture
  letI : IsProbabilityMeasure P :=
    (hB.toIsPreBrownianReal.hasLaw ∅).isProbabilityMeasure
  have hInd : X ⟂ᵢ[P] Y := by
    have hφ : Measurable
        (fun f : C(ℝ≥0, ℝ) => a - f r) :=
      measurable_const.sub (ContinuousMap.measurable_eval r)
    have hInd' :=
      (hB.indepFun_shiftToZero_freezeAfter hmeasurable r).symm.comp
        hφ (measurable_runningMinimum (q - r))
    have hXeq : X = fun ω => a - (freezeAfter (pathB ω) r) r := by
      funext ω
      simp [X, freezeAfter]
    rw [hXeq]
    exact hInd'
  have hYlaw : P.map Y =
      (P.map pathB).map (fun f => runningMinimum f (q - r)) := by
    calc
      P.map Y = (P.map future).map
          (fun f => runningMinimum f (q - r)) :=
        (Measure.map_map (measurable_runningMinimum (q - r)) hfuture).symm
      _ = (P.map pathB).map
          (fun f => runningMinimum f (q - r)) := by
        rw [hB.measure_shiftToZero_eq hmeasurable r]
  have hnull (b : ℝ) : (P.map Y) {b} = 0 := by
    rw [hYlaw, Measure.map_apply (measurable_runningMinimum (q - r))
      (measurableSet_singleton b)]
    exact hB.measure_runningMinimum_eq hmeasurable
      (tsub_pos_iff_lt.mpr hrq) b
  have heq : P {ω | intervalMinimum (pathB ω) r q = a} = 0 := by
    have hset : {ω | intervalMinimum (pathB ω) r q = a} =
        {ω | X ω = Y ω} := by
      ext ω
      change pathB ω r + Y ω = a ↔ a - pathB ω r = Y ω
      constructor <;> intro h <;> linarith
    rw [hset]
    exact hInd.measure_eq_zero_of_right_atomless hX hY hnull
  have hset : MeasurableSet
      {f : C(ℝ≥0, ℝ) | intervalMinimum f r q = a} :=
    (measurable_intervalMinimum r q) (measurableSet_singleton a)
  change (P.map pathB) {f | intervalMinimum f r q = a} = 0
  rw [Measure.map_apply hpath hset]
  exact heq

/-- The minimum of the negated Brownian path on a nondegenerate
deterministic interval also has no atoms. -/
theorem IsBrownianReal.measure_negIntervalMinimum_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t))
    {r q : ℝ≥0} (hrq : r < q) (a : ℝ) :
    let μ := P.map (hB.continuousPathMap hmeasurable)
    μ {f : C(ℝ≥0, ℝ) | intervalMinimum (-f) r q = a} = 0 := by
  dsimp
  let N : ℝ≥0 → Ω → ℝ := fun t ω => -B t ω
  let hN : IsBrownianReal N P := hB.neg
  let hNmeas (t : ℝ≥0) : Measurable (N t) := (hmeasurable t).neg
  let pathB := hB.continuousPathMap hmeasurable
  let pathN := hN.continuousPathMap hNmeas
  have hae : pathN =ᵐ[P] fun ω => -(pathB ω) := by
    filter_upwards [hN.continuousPathMap_ae_eq hNmeas,
      hB.continuousPathMap_ae_eq hmeasurable] with ω hωN hωB
    ext t
    change pathN ω t = -(pathB ω t)
    rw [hωN t, hωB t]
  have hnull := hN.measure_intervalMinimum_eq hNmeas hrq a
  change (P.map pathN) {f : C(ℝ≥0, ℝ) |
    intervalMinimum f r q = a} = 0 at hnull
  rw [Measure.map_congr hae] at hnull
  have hpath : Measurable pathB :=
    hB.measurable_continuousPathMap hmeasurable
  have hset : MeasurableSet
      {f : C(ℝ≥0, ℝ) | intervalMinimum (-f) r q = a} :=
    (measurable_intervalMinimum r q).comp continuous_neg.measurable
      (measurableSet_singleton a)
  change (P.map pathB) {f : C(ℝ≥0, ℝ) |
    intervalMinimum (-f) r q = a} = 0
  rw [Measure.map_apply hpath hset]
  have hnegpath : Measurable (fun ω => -(pathB ω)) :=
    continuous_neg.measurable.comp hpath
  have hset2 : MeasurableSet
      {f : C(ℝ≥0, ℝ) | intervalMinimum f r q = a} :=
    (measurable_intervalMinimum r q) (measurableSet_singleton a)
  rw [Measure.map_apply hnegpath hset2] at hnull
  exact hnull

end ProbabilityTheory

end

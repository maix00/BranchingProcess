/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Reflection.FirstPassageApproximation
public import Probability.Process.Brownian.GaussianMarginal
public import Probability.Process.Path.FirstPassageReflection
public import Probability.Process.Path.RunningMinimum

/-!
# Brownian first-passage reflection principle

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.measure_hitAndAbove_eq_below`:
  for $a<0$, the probability of hitting $(-\infty,a]$ by time $1$
  and ending above $a$ equals the probability of ending below $a$.
- `ProbabilityTheory.IsBrownianReal.measure_firstPassageBelow_le_one`:
  for $a<0$, the probability of passage by time $1$ is twice the
  probability of a Brownian endpoint below $a$.
- `ProbabilityTheory.IsBrownianReal.measure_runningMinimum_le_one`:
  the same probability identity for the running minimum at time $1$.

This is the event form of the reflection principle in Theorem 2.1 of
S. J. Dilworth and Duncan Wright, *A direct proof of the reflection
principle for Brownian motion*, Theory Stoch. Process. 21(37):2 (2016),
1--3, arXiv:1810.01783. The same reflection principle underlies the
Lévy identity cited in Lemma 2.3 of Erwin Bolthausen, *On a functional
central limit theorem for random walks conditioned to stay positive*,
Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- Brownian paths hitting a negative level by time `1` and ending above
it have the same probability as paths ending below it. -/
theorem IsBrownianReal.measure_hitAndAbove_eq_below
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t))
    {a : ℝ} (ha : a < 0) :
    let μ := P.map (hB.continuousPathMap hBmeasurable)
    μ {f : C(ℝ≥0, ℝ) | firstPassageBelow f a ≤ 1 ∧ a < f 1} =
      μ {f : C(ℝ≥0, ℝ) | f 1 < a} := by
  dsimp
  let μ := P.map (hB.continuousPathMap hBmeasurable)
  let F : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ) := fun f =>
    reflectAfter f (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA
  let U : Set C(ℝ≥0, ℝ) := {f | firstPassageBelow f a ≤ 1 ∧ a < f 1}
  let L : Set C(ℝ≥0, ℝ) := {f | f 1 < a}
  have hU : MeasurableSet U := by
    exact ((measurable_firstPassageBelow a) measurableSet_Iic).inter
      ((ContinuousMap.measurable_eval 1) measurableSet_Ioi)
  have hF : Measurable F := by
    have hT : Measurable (fun f : C(ℝ≥0, ℝ) =>
        (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA) :=
      ((measurable_firstPassageBelow a).min measurable_const).untopA
    exact measurable_reflectAfter_pair.comp (measurable_id.prodMk hT)
  have h0orig : ∀ᵐ ω ∂P, a < hB.continuousPathMap hBmeasurable ω 0 := by
    filter_upwards [hB.continuousPathMap_ae_eq hBmeasurable,
      hB.eval_zero_ae_eq_zero] with ω hpath hzero
    rw [hpath 0, hzero]
    exact ha
  have h0meas : MeasurableSet {f : C(ℝ≥0, ℝ) | a < f 0} :=
    (ContinuousMap.measurable_eval 0) measurableSet_Ioi
  have h0 : ∀ᵐ f ∂μ, a < f 0 :=
    (ae_map_iff (hB.measurable_continuousPathMap hBmeasurable).aemeasurable
      h0meas).2 h0orig
  have hpre : F ⁻¹' U =ᵐ[μ] L := by
    filter_upwards [h0] with f hf0
    apply propext
    change (firstPassageBelow (F f) a ≤ 1 ∧ a < F f 1) ↔ f 1 < a
    have hevent := firstPassageBelow_le_one_reflectAfter_capped_iff f a
    have hL_hit (hf : f 1 < a) : firstPassageBelow f a ≤ 1 :=
      (firstPassageBelow_le_iff f a 1).2 ⟨1, le_rfl, hf.le⟩
    constructor
    · rintro ⟨hFH, hFend⟩
      have hH : firstPassageBelow f a ≤ 1 := hevent.mp hFH
      have hend := reflectAfter_firstPassageBelow_capped_apply_one f a hf0 hH
      change F f 1 = 2 * a - f 1 at hend
      linarith
    · intro hfL
      have hH := hL_hit hfL
      refine ⟨hevent.mpr hH, ?_⟩
      have hend := reflectAfter_firstPassageBelow_capped_apply_one f a hf0 hH
      change F f 1 = 2 * a - f 1 at hend
      linarith
  have hinv : μ.map F = μ :=
    hB.measure_reflectAfter_firstPassageBeforeOne_eq hBmeasurable a
  calc
    μ U = (μ.map F) U := by rw [hinv]
    _ = μ (F ⁻¹' U) := Measure.map_apply hF hU
    _ = μ L := measure_congr hpre

/-- The one-time reflection principle for a negative level: the
probability of passage by time `1` is twice the lower-tail probability
of the endpoint. -/
theorem IsBrownianReal.measure_firstPassageBelow_le_one
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t))
    {a : ℝ} (ha : a < 0) :
    let μ := P.map (hB.continuousPathMap hBmeasurable)
    μ {f : C(ℝ≥0, ℝ) | firstPassageBelow f a ≤ 1} =
      2 * μ {f : C(ℝ≥0, ℝ) | f 1 < a} := by
  dsimp
  let μ := P.map (hB.continuousPathMap hBmeasurable)
  let H : Set C(ℝ≥0, ℝ) := {f | firstPassageBelow f a ≤ 1}
  let U : Set C(ℝ≥0, ℝ) := {f | firstPassageBelow f a ≤ 1 ∧ a < f 1}
  let L : Set C(ℝ≥0, ℝ) := {f | f 1 < a}
  have hLmeas : MeasurableSet L :=
    (ContinuousMap.measurable_eval 1) measurableSet_Iio
  have hAorig : ∀ᵐ ω ∂P, hB.continuousPathMap hBmeasurable ω 1 ≠ a := by
    filter_upwards [hB.continuousPathMap_ae_eq hBmeasurable,
      hB.ae_eval_ne (by norm_num : (0 : ℝ≥0) < 1) a] with ω hpath hne
    rw [hpath 1]
    exact hne
  have hAmeas : MeasurableSet {f : C(ℝ≥0, ℝ) | f 1 ≠ a} :=
    (ContinuousMap.measurable_eval 1) (measurableSet_singleton a).compl
  have hA : ∀ᵐ f ∂μ, f 1 ≠ a :=
    (ae_map_iff (hB.measurable_continuousPathMap hBmeasurable).aemeasurable
      hAmeas).2 hAorig
  have hEq : H =ᵐ[μ] U ∪ L := by
    filter_upwards [hA] with f hfne
    apply propext
    change firstPassageBelow f a ≤ 1 ↔
      (firstPassageBelow f a ≤ 1 ∧ a < f 1) ∨ f 1 < a
    constructor
    · intro hhit
      rcases lt_or_gt_of_ne hfne with hlt | hgt
      · exact Or.inr hlt
      · exact Or.inl ⟨hhit, hgt⟩
    · rintro (⟨hhit, _⟩ | hlt)
      · exact hhit
      · exact (firstPassageBelow_le_iff f a 1).2 ⟨1, le_rfl, hlt.le⟩
  have hdisj : Disjoint U L := by
    apply Set.disjoint_left.mpr
    intro f hfU hfL
    exact (lt_asymm hfU.2) hfL
  have hreflect : μ U = μ L :=
    hB.measure_hitAndAbove_eq_below hBmeasurable ha
  calc
    μ H = μ (U ∪ L) := measure_congr hEq
    _ = μ U + μ L := measure_union hdisj hLmeas
    _ = 2 * μ L := by rw [hreflect, two_mul]

/-- The running minimum at time `1` obeys the one-time Brownian
reflection principle. -/
theorem IsBrownianReal.measure_runningMinimum_le_one
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t))
    {a : ℝ} (ha : a < 0) :
    let μ := P.map (hB.continuousPathMap hBmeasurable)
    μ {f : C(ℝ≥0, ℝ) | runningMinimum f 1 ≤ a} =
      2 * μ {f : C(ℝ≥0, ℝ) | f 1 < a} := by
  have hset : {f : C(ℝ≥0, ℝ) | runningMinimum f 1 ≤ a} =
      {f | firstPassageBelow f a ≤ (1 : WithTop ℝ≥0)} := by
    ext f
    simpa using (runningMinimum_le_iff_firstPassageBelow_le f 1 a)
  rw [hset]
  exact hB.measure_firstPassageBelow_le_one hBmeasurable ha

end ProbabilityTheory

end

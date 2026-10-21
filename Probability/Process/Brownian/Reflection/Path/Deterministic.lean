/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Reflection.Basic
public import Probability.Process.Brownian.PathLaw.ContinuousPathLaw
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Reflection of Brownian motion at a fixed time

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.reflection_at_fixed_time`: if $B$ is a
  Brownian motion and $r\ge0$ is fixed, then
  $B'_t=B_t$ for $t\le r$ and $B'_t=2B_r-B_t$ for $t>r$ is a Brownian motion.
- `ProbabilityTheory.IsBrownianReal.measure_reflectAfter_continuousPathMap_eq`:
  reflection at a fixed time preserves the law on continuous-path space.

This is the deterministic-time case of Theorem 2.1 in S. J. Dilworth and
Duncan Wright, *A direct proof of the reflection principle for Brownian
motion*, Theory Stoch. Process. 21(37):2 (2016), 1--3. That reflection
principle supplies Lévy's running-minimum identity cited in Lemma 2.3 of
Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

private noncomputable def reflectedProcessAtTime {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (r : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω => if t ≤ r then B t ω else 2 * B r ω - B t ω

private lemma reflectedProcessAtTime_eq_of_le {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) {r t : ℝ≥0} (ht : t ≤ r) :
    reflectedProcessAtTime B r t = B t := by
  funext ω
  simp [reflectedProcessAtTime, ht]

private lemma reflectedProcessAtTime_eq_of_lt {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) {r t : ℝ≥0} (ht : r < t) :
    reflectedProcessAtTime B r t = fun ω => 2 * B r ω - B t ω := by
  funext ω
  simp [reflectedProcessAtTime, not_le.mpr ht]

private lemma IsPreBrownianReal.reflectedProcessAtTime_isGaussianProcess
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (r : ℝ≥0) :
    IsGaussianProcess (reflectedProcessAtTime B r) P := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  intro t
  by_cases ht : t ≤ r
  · refine ⟨{t},
      { toFun := fun x => x ⟨t, by simp⟩
        map_add' := by simp
        map_smul' := by simp }, ?_⟩
    intro ω
    simp [reflectedProcessAtTime, ht]
  · refine ⟨{r, t},
      { toFun := fun x => 2 * x ⟨r, by simp⟩ - x ⟨t, by simp⟩
        map_add' := by intro x y; simp; ring
        map_smul' := by intro c x; simp; ring }, ?_⟩
    intro ω
    simp [reflectedProcessAtTime, ht]

private lemma IsPreBrownianReal.reflectedProcessAtTime_isPreBrownianReal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (r : ℝ≥0) :
    IsPreBrownianReal (reflectedProcessAtTime B r) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let hG := hB.reflectedProcessAtTime_isGaussianProcess r
  refine hG.isPreBrownianReal_of_covariance ?_ ?_
  · intro t
    by_cases ht : t ≤ r
    · simpa [reflectedProcessAtTime, ht] using hB.integral_eval t
    · simp only [reflectedProcessAtTime, ite_eq_right ht]
      rw [integral_sub, integral_const_mul, hB.integral_eval, hB.integral_eval]
      · ring
      · exact (hB.integrable_eval r).const_mul 2
      · exact hB.integrable_eval t
  · intro s t hst
    have hmem (u : ℝ≥0) : MemLp (B u) 2 P :=
      (hB.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
    by_cases htr : t ≤ r
    · have hsr : s ≤ r := hst.trans htr
      rw [reflectedProcessAtTime_eq_of_le B hsr,
        reflectedProcessAtTime_eq_of_le B htr]
      rw [hB.covariance_eval, min_eq_left hst]
    · have hrt : r ≤ t := (lt_of_not_ge htr).le
      by_cases hsr : s ≤ r
      · rw [reflectedProcessAtTime_eq_of_le B hsr,
          reflectedProcessAtTime_eq_of_lt B (lt_of_not_ge htr)]
        rw [covariance_fun_sub_right (hmem s) ((hmem r).const_mul 2) (hmem t),
          covariance_const_mul_right, hB.covariance_eval, hB.covariance_eval,
          min_eq_left hsr, min_eq_left hst]
        ring
      · have hrs : r ≤ s := (lt_of_not_ge hsr).le
        rw [reflectedProcessAtTime_eq_of_lt B (lt_of_not_ge hsr),
          reflectedProcessAtTime_eq_of_lt B (lt_of_not_ge htr)]
        rw [covariance_fun_sub_fun_sub ((hmem r).const_mul 2) (hmem s)
          ((hmem r).const_mul 2) (hmem t)]
        simp_rw [covariance_const_mul_left, covariance_const_mul_right,
          hB.covariance_eval]
        rw [min_self, min_eq_left hrt, min_eq_right hrs, min_eq_left hst]
        ring

/-- Reflecting Brownian motion at a fixed deterministic time preserves
its Brownian law. -/
theorem IsBrownianReal.reflection_at_fixed_time
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (r : ℝ≥0) :
    IsBrownianReal
      (fun t ω => if t ≤ r then B t ω else 2 * B r ω - B t ω) P := by
  refine ⟨hB.toIsPreBrownianReal.reflectedProcessAtTime_isPreBrownianReal r, ?_⟩
  filter_upwards [hB.cont] with ω hω
  let f : C(ℝ≥0, ℝ) := ⟨fun t => B t ω, hω⟩
  have h : (fun t => reflectedProcessAtTime B r t ω) = reflectAfter f r := by
    funext t
    by_cases ht : t ≤ r
    · simp [reflectedProcessAtTime, reflectAfter_apply_le _ _ _ ht, ht, f]
    · simp [reflectedProcessAtTime, reflectAfter_apply_of_lt _ _ _
        (lt_of_not_ge ht), ht, f]
  change Continuous (fun t => reflectedProcessAtTime B r t ω)
  rw [h]
  exact (reflectAfter f r).continuous

/-- Reflecting a Brownian path at a fixed time preserves its law on
continuous-path space. -/
theorem IsBrownianReal.measure_reflectAfter_continuousPathMap_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t)) (r : ℝ≥0) :
    P.map (fun ω => reflectAfter (hB.continuousPathMap hBmeasurable ω) r) =
      P.map (hB.continuousPathMap hBmeasurable) := by
  let Br : ℝ≥0 → Ω → ℝ :=
    fun t ω => if t ≤ r then B t ω else 2 * B r ω - B t ω
  have hBr : IsBrownianReal Br P := hB.reflection_at_fixed_time r
  have hBrmeasurable (t : ℝ≥0) : Measurable (Br t) := by
    by_cases ht : t ≤ r
    · simpa [Br, ht] using hBmeasurable t
    · have htarget : Measurable (fun ω => 2 * B r ω - B t ω) := by
        fun_prop
      simpa [Br, ht] using htarget
  have hpathEq :
      (fun ω => reflectAfter (hB.continuousPathMap hBmeasurable ω) r) =ᵐ[P]
        hBr.continuousPathMap hBrmeasurable := by
    filter_upwards [hB.continuousPathMap_ae_eq hBmeasurable,
      hBr.continuousPathMap_ae_eq hBrmeasurable] with ω hω hωr
    ext t
    by_cases ht : t ≤ r
    · rw [reflectAfter_apply_le _ _ _ ht, hω t, hωr t]
      simp [Br, ht]
    · rw [reflectAfter_apply_of_lt _ _ _ (lt_of_not_ge ht),
        hω r, hω t, hωr t]
      simp [Br, ht]
  calc
    P.map (fun ω => reflectAfter (hB.continuousPathMap hBmeasurable ω) r) =
        P.map (hBr.continuousPathMap hBrmeasurable) := Measure.map_congr hpathEq
    _ = P.map (hB.continuousPathMap hBmeasurable) :=
      hBr.measure_continuousPathMap_eq hB hBrmeasurable hBmeasurable

end ProbabilityTheory

end

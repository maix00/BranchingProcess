/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Probability.Process.Brownian.PathLaw.ContinuousPathLaw
public import Probability.Process.Path.TimeReversal.FiniteHorizon

/-!
# Brownian increments reversed over a finite time horizon

The public definition and theorem in this file are:

- `ProbabilityTheory.reverseBrownianBefore`:
  for $u\le t$ it is $B(t)-B(t-u)$, continued by $B(u)-B(0)$ for $u>t$.
- `ProbabilityTheory.measurable_reverseBrownianBefore`:
  every coordinate of the reversed-increment process is measurable.
- `ProbabilityTheory.IsPreBrownianReal.reverseBrownianBefore_isGaussianProcess`:
  the reversed-increment process is Gaussian.
- `ProbabilityTheory.IsPreBrownianReal.integral_reverseBrownianBefore`:
  the reversed-increment process is centered.
- `ProbabilityTheory.IsPreBrownianReal.covariance_reverseBrownianBefore`:
  its covariance at $s\le u$ equals $s$.
- `ProbabilityTheory.IsPreBrownianReal.reverseBrownianBefore_isPreBrownianReal`:
  its finite-dimensional laws are Brownian.
- `ProbabilityTheory.IsBrownianReal.reverseBrownianBefore_isBrownianReal`:
  its paths are Brownian and continuous almost surely.
- `ProbabilityTheory.IsBrownianReal.measure_reverseBrownianBefore_eq`:
  its continuous path law equals the original Brownian path law.

This prepares the time-reversal proof of Lévy's reflected-process identity
used in Lemma 2.3 of Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3)
(1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- Reverse Brownian increments up to time `t` and join them to the
original increments after `t`. Both formulas agree at the joining time. -/
noncomputable def reverseBrownianBefore {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (t u : ℝ≥0) (ω : Ω) : ℝ :=
  if u ≤ t then B t ω - B (t - u) ω else B u ω - B 0 ω

/-- Every reversed-increment coordinate is measurable when the original
process has measurable coordinates. -/
theorem measurable_reverseBrownianBefore
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hBmeasurable : ∀ u, Measurable (B u))
    (t u : ℝ≥0) : Measurable (reverseBrownianBefore B t u) := by
  unfold reverseBrownianBefore
  split_ifs with hu
  · exact (hBmeasurable t).sub (hBmeasurable (t - u))
  · exact (hBmeasurable u).sub (hBmeasurable 0)

/-- Reversed increments are finite linear combinations of Brownian
coordinates, hence form a Gaussian process. -/
theorem IsPreBrownianReal.reverseBrownianBefore_isGaussianProcess
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    IsGaussianProcess (reverseBrownianBefore B t) P := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  intro u
  by_cases hu : u ≤ t
  · refine ⟨{t, t - u},
      { toFun := fun x => x ⟨t, by simp⟩ - x ⟨t - u, by simp⟩
        map_add' := by intro x y; simp; abel
        map_smul' := by intro c x; simp only [Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]; ring }, ?_⟩
    intro ω
    simp [reverseBrownianBefore, hu]
  · refine ⟨{u, 0},
      { toFun := fun x => x ⟨u, by simp⟩ - x ⟨0, by simp⟩
        map_add' := by intro x y; simp; abel
        map_smul' := by intro c x; simp only [Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]; ring }, ?_⟩
    intro ω
    simp [reverseBrownianBefore, hu]

/-- Every reversed increment has mean zero. -/
theorem IsPreBrownianReal.integral_reverseBrownianBefore
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (t u : ℝ≥0) :
    P[reverseBrownianBefore B t u] = 0 := by
  by_cases hu : u ≤ t
  · simp only [reverseBrownianBefore, ite_eq_left hu]
    rw [integral_sub (hB.integrable_eval t) (hB.integrable_eval (t - u)),
      hB.integral_eval, hB.integral_eval, sub_self]
  · simp only [reverseBrownianBefore, ite_eq_right hu]
    rw [integral_sub (hB.integrable_eval u) (hB.integrable_eval 0),
      hB.integral_eval, hB.integral_eval, sub_self]

private theorem IsPreBrownianReal.covariance_reverseBrownianBefore_inside
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {t s u : ℝ≥0} (hsu : s ≤ u) (hut : u ≤ t) :
    cov[reverseBrownianBefore B t s, reverseBrownianBefore B t u; P] = s := by
  have hst : s ≤ t := hsu.trans hut
  have hsuborder : t - u ≤ t - s := tsub_le_tsub_left hsu t
  letI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  change cov[fun ω => if s ≤ t then B t ω - B (t - s) ω else B s ω - B 0 ω,
    fun ω => if u ≤ t then B t ω - B (t - u) ω else B u ω - B 0 ω; P] = s
  simp only [ite_eq_left hst, ite_eq_left hut]
  rw [covariance_fun_sub_fun_sub]
  · simp_rw [hB.covariance_fun_eval]
    rw [min_self, min_eq_right tsub_le_self, min_eq_left tsub_le_self,
      min_eq_right hsuborder]
    rw [NNReal.coe_sub hut, NNReal.coe_sub hst]
    ring
  all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two

private theorem IsPreBrownianReal.covariance_reverseBrownianBefore_cross
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {t s u : ℝ≥0} (hst : s ≤ t) (htu : t < u) :
    cov[reverseBrownianBefore B t s, reverseBrownianBefore B t u; P] = s := by
  letI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  change cov[fun ω => if s ≤ t then B t ω - B (t - s) ω else B s ω - B 0 ω,
    fun ω => if u ≤ t then B t ω - B (t - u) ω else B u ω - B 0 ω; P] = s
  simp only [ite_eq_left hst, ite_eq_right (not_le.mpr htu)]
  rw [covariance_fun_sub_fun_sub]
  · simp_rw [hB.covariance_fun_eval]
    rw [min_eq_left htu.le, min_eq_left
      ((tsub_le_self : t - s ≤ t).trans htu.le)]
    rw [NNReal.coe_sub hst]
    simp
  all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two

private theorem IsPreBrownianReal.covariance_reverseBrownianBefore_after
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {t s u : ℝ≥0} (hts : t < s) (hsu : s ≤ u) :
    cov[reverseBrownianBefore B t s, reverseBrownianBefore B t u; P] = s := by
  letI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  change cov[fun ω => if s ≤ t then B t ω - B (t - s) ω else B s ω - B 0 ω,
    fun ω => if u ≤ t then B t ω - B (t - u) ω else B u ω - B 0 ω; P] = s
  simp only [ite_eq_right (not_le.mpr hts),
    ite_eq_right (not_le.mpr (hts.trans_le hsu))]
  rw [covariance_fun_sub_fun_sub]
  · simp_rw [hB.covariance_fun_eval]
    rw [min_eq_left hsu]
    simp
  all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two

/-- The finite-horizon reversed-increment process has Brownian covariance:
for $s\le u$, its covariance is $s$. -/
theorem IsPreBrownianReal.covariance_reverseBrownianBefore
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) {s u : ℝ≥0} (hsu : s ≤ u) :
    cov[reverseBrownianBefore B t s, reverseBrownianBefore B t u; P] = s := by
  by_cases hut : u ≤ t
  · exact hB.covariance_reverseBrownianBefore_inside hsu hut
  by_cases hst : s ≤ t
  · exact hB.covariance_reverseBrownianBefore_cross hst (lt_of_not_ge hut)
  · exact hB.covariance_reverseBrownianBefore_after (lt_of_not_ge hst) hsu

/-- Reversing increments before a fixed horizon preserves all Brownian
finite-dimensional distributions. -/
theorem IsPreBrownianReal.reverseBrownianBefore_isPreBrownianReal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    IsPreBrownianReal (reverseBrownianBefore B t) P := by
  apply (hB.reverseBrownianBefore_isGaussianProcess t).isPreBrownianReal_of_covariance
  · exact hB.integral_reverseBrownianBefore t
  · intro s u hsu
    exact hB.covariance_reverseBrownianBefore t hsu

/-- The reversed-increment process has continuous paths whenever the
original Brownian path is continuous. -/
theorem IsBrownianReal.reverseBrownianBefore_isBrownianReal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (t : ℝ≥0) :
    IsBrownianReal (reverseBrownianBefore B t) P := by
  refine ⟨hB.toIsPreBrownianReal.reverseBrownianBefore_isPreBrownianReal t, ?_⟩
  filter_upwards [hB.cont] with ω hω
  let f : C(ℝ≥0, ℝ) := ⟨fun u => B u ω, hω⟩
  change Continuous (fun u : ℝ≥0 =>
    if u ≤ t then f t - f (t - u) else f u - f 0)
  apply Continuous.if_le (f := id) (g := fun _ => t)
    (by fun_prop) (by fun_prop) continuous_id continuous_const
  intro u hu
  change u = t at hu
  subst u
  simp

/-- Reversing the increments before a fixed time leaves Brownian path
law unchanged. This is the finite-horizon time-reversal step used to
identify the law of the height above the running minimum. -/
theorem IsBrownianReal.measure_reverseBrownianBefore_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) (t : ℝ≥0) :
    P.map ((hB.reverseBrownianBefore_isBrownianReal t).continuousPathMap
      (measurable_reverseBrownianBefore hBmeasurable t)) =
      P.map (hB.continuousPathMap hBmeasurable) := by
  exact (hB.reverseBrownianBefore_isBrownianReal t).measure_continuousPathMap_eq
    hB (measurable_reverseBrownianBefore hBmeasurable t) hBmeasurable

end ProbabilityTheory

end

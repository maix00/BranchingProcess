/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Probability.Distributions.CharacteristicFunction.Tauberian.FrequencyAverage
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Asymptotics of frequency-averaged cosine defects

Compact-uniform regular variation of index two makes the leading terms in a
frequency-averaged cosine defect cancel. This module provides the deterministic
averaging limit used to turn the coercive tail estimate into a little-o tail
bound.
-/

open Filter MeasureTheory Set
open scoped Topology Interval
open Analysis.Fourier.CosineTauberian

@[expose] public section

namespace ProbabilityTheory

/- The compact-uniform ratio limit cancels the two leading quadratic terms
in the averaged cosine defect. The base `2 * u` ratio covers multipliers in
`[2, 4]`. -/
theorem tendsto_frequencyCancellation_ratio_nhdsGT_zero
    {f : ℝ → ℝ} (hf : Continuous f)
    (hpos : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), 0 < f u)
    (hratio : TendstoUniformlyOn
      (fun u t => f (t * u) / f u) (fun t => t ^ 2)
      (𝓝[>] (0 : ℝ)) (Icc (1 : ℝ) 2)) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in (1 : ℝ)..2, (4 * f (t * u) - f ((2 * t) * u))) / f u)
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
  let R : ℝ → ℝ → ℝ := fun u t => f (t * u) / f u
  let M : ℝ → ℝ → ℝ :=
    (fun u t => 4 * R u t) - (fun u t => R (2 * u) t * R u 2)
  let H : ℝ → ℝ → ℝ := fun u t =>
    (4 * f (t * u) - f ((2 * t) * u)) / f u
  have hscale : Tendsto (fun u : ℝ => 2 * u)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : Tendsto (fun u : ℝ => 2 * u) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        simpa using (tendsto_const_nhds.mul
          (tendsto_id : Tendsto id (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))))
      exact hcont.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact mul_pos (by norm_num : (0 : ℝ) < 2) hu
  have hratioMetric := Metric.tendstoUniformlyOn_iff.mp hratio
  have hratioAtTwo : Tendsto (fun u : ℝ => R u 2)
      (𝓝[>] (0 : ℝ)) (nhds 4) := by
    have h := hratio.tendsto_at (by norm_num : (2 : ℝ) ∈ Icc 1 2)
    convert h using 1
    all_goals norm_num [R, pow_two]
  have hratioTwoUniform : TendstoUniformlyOn
      (fun u t => R (2 * u) t) (fun t => t ^ 2)
      (𝓝[>] (0 : ℝ)) (Icc (1 : ℝ) 2) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hEventually := hscale.eventually (hratioMetric ε hε)
    filter_upwards [hEventually] with u hu t ht
    exact hu t ht
  have hratioAtTwoUniform : TendstoUniformlyOn
      (fun u _ : ℝ => R u 2) (fun _ : ℝ => 4)
      (𝓝[>] (0 : ℝ)) (Icc (1 : ℝ) 2) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hEventually := hratioAtTwo.eventually (Metric.ball_mem_nhds 4 hε)
    filter_upwards [hEventually] with u hu t ht
    simpa [dist_comm] using hu
  have hfourRatio : TendstoUniformlyOn
      (fun u t => 4 * R u t) (fun t => 4 * t ^ 2)
      (𝓝[>] (0 : ℝ)) (Icc (1 : ℝ) 2) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hnear := hratioMetric (ε / 4) (by positivity)
    filter_upwards [hnear] with u hu t ht
    have hdist : dist (4 * R u t) (4 * t ^ 2) =
        4 * dist (R u t) (t ^ 2) := by
      rw [Real.dist_eq, Real.dist_eq]
      rw [show 4 * R u t - 4 * t ^ 2 = 4 * (R u t - t ^ 2) by ring]
      simp
    have h' := hu t ht
    have h'' : dist (R u t) (t ^ 2) < ε / 4 := by
      simpa [dist_comm] using h'
    calc
      dist (4 * t ^ 2) (4 * R u t) = dist (4 * R u t) (4 * t ^ 2) := dist_comm _ _
      _ = 4 * dist (R u t) (t ^ 2) := hdist
      _ < ε := by nlinarith
  have hproduct : TendstoUniformlyOn
      (fun u t => R (2 * u) t * R u 2) (fun t => 4 * t ^ 2)
      (𝓝[>] (0 : ℝ)) (Icc (1 : ℝ) 2) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    let δ : ℝ := min 1 (ε / 10)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min (by norm_num) (by positivity)
    have hδone : δ ≤ 1 := by dsimp [δ]; exact min_le_left _ _
    have hδeps : δ ≤ ε / 10 := by dsimp [δ]; exact min_le_right _ _
    have hAnear := (Metric.tendstoUniformlyOn_iff.mp hratioTwoUniform) δ hδ
    have hBnear := hratioAtTwo.eventually (Metric.ball_mem_nhds 4 hδ)
    filter_upwards [hAnear, hBnear] with u hAU hBU t ht
    let A := R (2 * u) t
    let B := R u 2
    have hA : |A - t ^ 2| < δ := by
      have h := hAU t ht
      simpa [A, dist_comm, Real.dist_eq, abs_sub_comm] using h
    have hB : |B - 4| < δ := by
      simpa [B, Real.dist_eq] using hBU
    have htlo : 0 ≤ t := le_trans (by norm_num) ht.1
    have hthi : t ≤ 2 := ht.2
    have ht2lo : 0 ≤ t ^ 2 := sq_nonneg t
    have ht2hi : t ^ 2 ≤ 4 := by nlinarith
    have hBabs : |B| ≤ 5 := by
      rw [abs_le]
      constructor <;> nlinarith [le_abs_self (B - 4), neg_le_abs (B - 4), hB.le]
    have ht2abs : |t ^ 2| ≤ 4 := by
      rw [abs_of_nonneg ht2lo]
      exact ht2hi
    have hprod :
        |A * B - t ^ 2 * 4| ≤ |A - t ^ 2| * |B| + |t ^ 2| * |B - 4| := by
      calc
        _ = |(A - t ^ 2) * B + t ^ 2 * (B - 4)| := by congr 1; ring
        _ ≤ |(A - t ^ 2) * B| + |t ^ 2 * (B - 4)| := abs_add_le _ _
        _ = |A - t ^ 2| * |B| + |t ^ 2| * |B - 4| := by rw [abs_mul, abs_mul]
    have htermA : |A - t ^ 2| * |B| ≤ δ * 5 :=
      mul_le_mul hA.le hBabs (abs_nonneg _) (by positivity)
    have htermB : |t ^ 2| * |B - 4| ≤ 4 * δ :=
      mul_le_mul ht2abs hB.le (abs_nonneg _) (by positivity)
    have hfinal : |A * B - t ^ 2 * 4| < ε := by
      calc
        _ ≤ δ * 5 + 4 * δ := by linarith
        _ < ε := by dsimp [δ] at hδeps ⊢; nlinarith
    have hdist : dist (A * B) (4 * t ^ 2) = |A * B - t ^ 2 * 4| := by
      rw [Real.dist_eq]
      congr 1
      ring
    rw [dist_comm, hdist]
    simpa [A, B, mul_comm] using hfinal
  have hmodel : TendstoUniformlyOn M (0 : ℝ → ℝ)
      (𝓝[>] (0 : ℝ)) (Icc (1 : ℝ) 2) := by
    simpa [M] using hfourRatio.sub hproduct
  have hposTwo : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), 0 < f (2 * u) :=
    hscale.eventually hpos
  have heq : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ),
      Set.EqOn (M u) (H u) (Icc (1 : ℝ) 2) := by
    filter_upwards [hpos, hposTwo] with u hu hu2 t ht
    dsimp [M, H, R]
    have harg : t * (2 * u) = (2 * t) * u := by ring
    rw [harg, div_mul_div_cancel₀ (ne_of_gt hu2)]
    field_simp [ne_of_gt hu]
  have hH : TendstoUniformlyOn H (0 : ℝ → ℝ)
      (𝓝[>] (0 : ℝ)) (Icc (1 : ℝ) 2) := by
    exact hmodel.congr (heq.mono fun u hu t ht => hu (x := t) ht)
  have hHContinuous : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ),
      ContinuousOn (H u) (uIcc (1 : ℝ) 2) := by
    filter_upwards [] with u
    have ht : Continuous (fun t : ℝ => t * u) :=
      continuous_id.mul continuous_const
    have htwo : Continuous (fun t : ℝ => (2 * t) * u) :=
      (continuous_const.mul continuous_id).mul continuous_const
    have hnum : Continuous (fun t : ℝ =>
        4 * f (t * u) - f ((2 * t) * u)) :=
      (continuous_const.mul (hf.comp ht)).sub (hf.comp htwo)
    change ContinuousOn (fun t : ℝ =>
      (4 * f (t * u) - f ((2 * t) * u)) / f u) (uIcc (1 : ℝ) 2)
    exact (hnum.div_const (f u)).continuousOn
  have hH' : TendstoUniformlyOn H (0 : ℝ → ℝ)
      (𝓝[>] (0 : ℝ)) (uIcc (1 : ℝ) 2) := by
    simpa [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hH
  have hIntegral := hH'.tendsto_intervalIntegral_of_continuousOn
    (μ := volume) (a := (1 : ℝ)) (b := 2) hHContinuous
  simpa [H, intervalIntegral.integral_div] using hIntegral

private theorem frequencyAverage_nonneg (z : ℝ) :
    0 ≤ cosineSquareFrequencyAverage z := by
  exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
    (fun t => sq_nonneg (1 - Real.cos (t * z)))

private theorem frequencyAverage_le_four (z : ℝ) :
    cosineSquareFrequencyAverage z ≤ 4 := by
  let f : ℝ → ℝ := fun t => (1 - Real.cos (t * z)) ^ 2
  have hfcont : Continuous f := by fun_prop
  have hf : IntervalIntegrable f volume 1 2 := hfcont.intervalIntegrable 1 2
  have hconst : IntervalIntegrable (fun _ : ℝ => (4 : ℝ)) volume 1 2 :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on
    (by norm_num : (1 : ℝ) ≤ 2) hf hconst (by
      intro t ht
      have hcoslo := Real.neg_one_le_cos (t * z)
      have hcoshi := Real.cos_le_one (t * z)
      nlinarith)
  have hconstInt : (∫ t in (1 : ℝ)..2, (4 : ℝ)) = 4 := by
    rw [intervalIntegral.integral_const]
    norm_num [smul_eq_mul]
  simpa [cosineSquareFrequencyAverage, f, hconstInt] using hmono

/-- One coercivity constant works for every positive scale. This uniformity is
needed when the tail estimate is used in a limit as the scale tends to
infinity. -/
theorem exists_pos_closedAbsTail_le_cosineDefectFrequencyAverage_all
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 0 < x →
      2 * c * μ.real {y : ℝ | x ≤ |y|} ≤
        ∫ t in (1 : ℝ)..2,
          (4 * cosineDefectIntegral μ (t / x) -
            cosineDefectIntegral μ ((2 * t) / x)) := by
  obtain ⟨c, hc, hcoercive⟩ :=
    exists_pos_cosineSquareFrequencyAverage_lower_bound
  refine ⟨c, hc, ?_⟩
  intro x hx
  let A : Set ℝ := {y : ℝ | x ≤ |y|}
  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_le measurable_const continuous_abs.measurable
  have hkernel_meas : AEStronglyMeasurable
      (fun y : ℝ => cosineSquareFrequencyAverage (y / x)) μ := by
    have hdiv : Continuous (fun y : ℝ => y / x) := continuous_id.div_const x
    exact (continuous_cosineSquareFrequencyAverage.comp hdiv).aestronglyMeasurable
  have hkernel_bound : ∀ᵐ y ∂μ,
      ‖cosineSquareFrequencyAverage (y / x)‖ ≤ 4 := by
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (frequencyAverage_nonneg _)]
    exact frequencyAverage_le_four _
  have hkernel_int : Integrable
      (fun y : ℝ => cosineSquareFrequencyAverage (y / x)) μ :=
    Integrable.of_bound hkernel_meas 4 hkernel_bound
  have hindicator : Integrable (A.indicator (fun _ : ℝ => c)) μ :=
    (integrable_const c).indicator hA
  have hindicator_eq :
      (∫ y, A.indicator (fun _ : ℝ => c) y ∂μ) = c * μ.real A := by
    rw [integral_indicator_const _ hA]
    simp [smul_eq_mul, mul_comm]
  have hpointwise (y : ℝ) :
      A.indicator (fun _ : ℝ => c) y ≤ cosineSquareFrequencyAverage (y / x) := by
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy]
      have hratio : 1 ≤ |y / x| := by
        rw [abs_div, abs_of_pos hx]
        calc
          1 = x / x := (div_self hx.ne').symm
          _ ≤ |y| / x := div_le_div_of_nonneg_right (by simpa [A] using hy) hx.le
      exact hcoercive (y / x) hratio
    · rw [Set.indicator_of_notMem hy]
      exact frequencyAverage_nonneg _
  have htail : c * μ.real A ≤
      ∫ y, cosineSquareFrequencyAverage (y / x) ∂μ := by
    calc
      _ = ∫ y, A.indicator (fun _ : ℝ => c) y ∂μ := hindicator_eq.symm
      _ ≤ ∫ y, cosineSquareFrequencyAverage (y / x) ∂μ :=
        integral_mono_ae hindicator hkernel_int (ae_of_all μ hpointwise)
  rw [intervalIntegral_four_cosineDefect_sub_double μ]
  calc
    2 * c * μ.real {y : ℝ | x ≤ |y|} = 2 * (c * μ.real A) := by
      simp [A, mul_assoc]
    _ ≤ 2 * ∫ y, cosineSquareFrequencyAverage (y / x) ∂μ :=
      mul_le_mul_of_nonneg_left htail (by norm_num)

/-- If the cosine defect has a compact-uniform regularly varying ratio of
index two at zero, then the closed two-sided tail of the same probability law
is little-o of that unscaled defect. The coercivity constant is uniform in
the scale, and the denominator is evaluated at the reciprocal scale. -/
theorem tendsto_closedAbsTail_div_cosineDefect_atTop
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), 0 < cosineDefectIntegral μ u)
    (hratio : TendstoUniformlyOn
      (fun u t => cosineDefectIntegral μ (t * u) / cosineDefectIntegral μ u)
      (fun t => t ^ 2) (𝓝[>] (0 : ℝ)) (Icc (1 : ℝ) 2)) :
    Tendsto
      (fun x : ℝ => μ.real {y : ℝ | x ≤ |y|} / cosineDefectIntegral μ x⁻¹)
      atTop (nhds 0) := by
  let D : ℝ → ℝ := cosineDefectIntegral μ
  let A : ℝ → ℝ := fun x =>
    ∫ t in (1 : ℝ)..2, (4 * D (t / x) - D ((2 * t) / x))
  let Q : ℝ → ℝ := fun x => A x / D x⁻¹
  have hcancel : Tendsto (fun u : ℝ =>
      (∫ t in (1 : ℝ)..2, (4 * D (t * u) - D ((2 * t) * u))) / D u)
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
    simpa [D] using tendsto_frequencyCancellation_ratio_nhdsGT_zero
      (continuous_cosineDefectIntegral μ) hpos hratio
  have hQ : Tendsto Q atTop (nhds 0) := by
    have h := hcancel.comp tendsto_inv_atTop_nhdsGT_zero
    have heq : (fun x : ℝ =>
        (∫ t in (1 : ℝ)..2,
          (4 * D (t * x⁻¹) - D ((2 * t) * x⁻¹))) / D x⁻¹) =ᶠ[atTop] Q := by
      filter_upwards [] with x
      simp [Q, A, div_eq_mul_inv]
    exact h.congr' heq
  obtain ⟨c, hc, hcoercive⟩ :=
    exists_pos_closedAbsTail_le_cosineDefectFrequencyAverage_all μ
  have hpositive : ∀ᶠ x : ℝ in atTop, 0 < D x⁻¹ :=
    tendsto_inv_atTop_nhdsGT_zero.eventually hpos
  have hbound : ∀ᶠ x : ℝ in atTop,
      0 ≤ μ.real {y : ℝ | x ≤ |y|} / D x⁻¹ ∧
      μ.real {y : ℝ | x ≤ |y|} / D x⁻¹ ≤ Q x / (2 * c) := by
    filter_upwards [hpositive, eventually_gt_atTop (0 : ℝ)] with x hDx hx
    have hscale := hcoercive x hx
    have hc2 : 0 < 2 * c := by positivity
    have hscaled :
        (2 * c) * (μ.real {y : ℝ | x ≤ |y|} / D x⁻¹) ≤ A x / D x⁻¹ := by
      calc
        _ = (2 * c * μ.real {y : ℝ | x ≤ |y|}) / D x⁻¹ := by ring
        _ ≤ A x / D x⁻¹ := div_le_div_of_nonneg_right hscale hDx.le
    have hdiv := div_le_div_of_nonneg_right hscaled hc2.le
    have hleft :
        ((2 * c) * (μ.real {y : ℝ | x ≤ |y|} / D x⁻¹)) / (2 * c) =
          μ.real {y : ℝ | x ≤ |y|} / D x⁻¹ := by
      field_simp [hc2.ne']
    refine ⟨div_nonneg measureReal_nonneg hDx.le, ?_⟩
    rw [hleft] at hdiv
    simpa [Q, A, D] using hdiv
  have hupper : Tendsto (fun x : ℝ => Q x / (2 * c)) atTop (nhds 0) := by
    simpa using hQ.div_const (2 * c)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact hbound.mono fun x hx => hx.1
  · exact hbound.mono fun x hx => hx.2

/-- Source-facing form for the squared-modulus characteristic defect. The
tail is explicitly that of `symmetrizedMeasure ν`, the law of `X - X'`. -/
theorem tendsto_symmetrizedClosedAbsTail_div_normDefect_atTop
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ),
      0 < 1 - ‖charFun ν u‖ ^ 2)
    (hratio : TendstoUniformlyOn
      (fun u t => (1 - ‖charFun ν (t * u)‖ ^ 2) /
        (1 - ‖charFun ν u‖ ^ 2))
      (fun t => t ^ 2) (𝓝[>] (0 : ℝ)) (Icc (1 : ℝ) 2)) :
    Tendsto
      (fun x : ℝ =>
        (symmetrizedMeasure ν).real {y : ℝ | x ≤ |y|} /
          (1 - ‖charFun ν x⁻¹‖ ^ 2))
      atTop (nhds 0) := by
  have hpos' : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ),
      0 < cosineDefectIntegral (symmetrizedMeasure ν) u := by
    filter_upwards [hpos] with u hu
    rw [cosineDefectIntegral_symmetrizedMeasure]
    exact hu
  have hratio' : TendstoUniformlyOn
      (fun u t =>
        cosineDefectIntegral (symmetrizedMeasure ν) (t * u) /
          cosineDefectIntegral (symmetrizedMeasure ν) u)
      (fun t => t ^ 2) (𝓝[>] (0 : ℝ)) (Icc (1 : ℝ) 2) := by
    simpa only [cosineDefectIntegral_symmetrizedMeasure] using hratio
  have h := tendsto_closedAbsTail_div_cosineDefect_atTop
    (symmetrizedMeasure ν) hpos' hratio'
  simpa only [cosineDefectIntegral_symmetrizedMeasure] using h

end ProbabilityTheory

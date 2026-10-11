/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.MeasureTheory.Convergence.L2FromTails
public import Mathlib.Probability.Moments.Variance

/-!
# L² norm convergence from second moments

Convert convergence of second moments into convergence of the corresponding
`L²` seminorms. This closes the measure-theoretic final step after a trajectory
proof establishes vanishing second moments.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityTheory

/-- If the second moments of a family of real-valued random variables tend to
zero, then their `L²` seminorms tend to zero. -/
theorem tendsto_eLpNorm_two_zero_of_integral_sq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hX4 : ∀ n, MemLp (X n) (4 : ℝ≥0∞) μ)
    (hsecond : Tendsto (fun n => ∫ ω, (X n ω) ^ 2 ∂μ)
      atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (X n) (2 : ℝ≥0∞) μ) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n => Real.sqrt (∫ ω, (X n ω) ^ 2 ∂μ))
      atTop (nhds 0) := by simpa using hsecond.sqrt
  have hofReal : Tendsto
      (fun n => ENNReal.ofReal (Real.sqrt (∫ ω, (X n ω) ^ 2 ∂μ)))
      atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hsqrt
  apply hofReal.congr'
  filter_upwards with n
  have hX2 : MemLp (X n) (2 : ℝ≥0∞) μ :=
    (hX4 n).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)
  have htoRealTwo : ENNReal.toReal (2 : ℝ≥0∞) = 2 := by norm_num
  have hnormSq : (∫ ω, ‖X n ω‖ ^ (2 : ℝ) ∂μ) =
      ∫ ω, (X n ω) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with ω
    simp [Real.norm_eq_abs]
  rw [hX2.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  rw [htoRealTwo, hnormSq]
  apply congrArg ENNReal.ofReal
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, Real.sqrt_eq_rpow]

/-- Convergence of centered second moments gives convergence of both the
expectations and variances. -/
theorem tendsto_integral_and_variance_of_tendsto_centered_integral_sq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (c : ℝ)
    (hX2 : ∀ n, MemLp (X n) (2 : ℝ≥0∞) μ)
    (hsecond : Tendsto (fun n => ∫ ω, (X n ω - c) ^ 2 ∂μ)
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ ω, X n ω ∂μ) atTop (nhds c) ∧
      Tendsto (fun n => variance (X n) μ) atTop (nhds 0) := by
  let Y : ℕ → Ω → ℝ := fun n ω => X n ω - c
  have hY2 : ∀ n, MemLp (Y n) (2 : ℝ≥0∞) μ := by
    intro n
    exact (hX2 n).sub (memLp_const c)
  have hYInt : ∀ n, Integrable (Y n) μ := by
    intro n
    exact (hY2 n).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hCenteredSecondNonneg (n : ℕ) :
      0 ≤ ∫ ω, (Y n ω) ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg (Y n ω)
  have hSqrt : Tendsto (fun n => Real.sqrt (∫ ω, (Y n ω) ^ 2 ∂μ))
      atTop (nhds 0) := by
    simpa [Y] using hsecond.sqrt
  have hAbsMeanBound : ∀ n,
      |∫ ω, Y n ω ∂μ| ≤ Real.sqrt (∫ ω, (Y n ω) ^ 2 ∂μ) := by
    intro n
    have hYHolder : MemLp (Y n) (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using hY2 n
    have hOneHolder : MemLp (fun _ : Ω => (1 : ℝ))
        (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using (memLp_const (1 : ℝ) :
        MemLp (fun _ : Ω => (1 : ℝ)) (2 : ℝ≥0∞) μ)
    have hHolder := integral_mul_norm_le_Lp_mul_Lq
      (Real.HolderConjugate.two_two : (2 : ℝ).HolderConjugate 2)
      hYHolder hOneHolder
    have hAbsIntegral :
        (∫ ω, |Y n ω| ∂μ) ≤ Real.sqrt (∫ ω, (Y n ω) ^ 2 ∂μ) := by
      simpa [Real.norm_eq_abs, Real.sqrt_eq_rpow] using hHolder
    calc
      |∫ ω, Y n ω ∂μ| = ‖∫ ω, Y n ω ∂μ‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ ω, ‖Y n ω‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ ω, |Y n ω| ∂μ := by congr 1
      _ ≤ Real.sqrt (∫ ω, (Y n ω) ^ 2 ∂μ) := hAbsIntegral
  have hAbsMean : Tendsto
      (fun n => |∫ ω, Y n ω ∂μ|) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n => abs_nonneg _
    · exact Filter.Eventually.of_forall hAbsMeanBound
    · exact hSqrt
  have hMeanY : Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using hAbsMean
  have hMeanEq (n : ℕ) :
      (∫ ω, X n ω ∂μ) = (∫ ω, Y n ω ∂μ) + c := by
    have hfun : (fun ω => X n ω) = fun ω => Y n ω + c := by
      funext ω
      simp [Y]
    rw [hfun, integral_add (hYInt n) (integrable_const c)]
    simp
  have hMean : Tendsto (fun n => ∫ ω, X n ω ∂μ) atTop (nhds c) := by
    simpa [hMeanEq] using hMeanY.add_const c
  have hVarianceBound (n : ℕ) :
      0 ≤ variance (X n) μ ∧
        variance (X n) μ ≤ ∫ ω, (Y n ω) ^ 2 ∂μ := by
    have hshift : X n = Y n + fun _ => c := by
      funext ω
      simp [Y]
    have hvariance : variance (X n) μ = variance (Y n) μ := by
      rw [hshift]
      exact variance_add_const (hY2 n).aestronglyMeasurable c
    rw [hvariance]
    constructor
    · exact variance_nonneg _ _
    · simpa using variance_le_expectation_sq (hY2 n).aestronglyMeasurable
  have hVariance : Tendsto (fun n => variance (X n) μ) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n => (hVarianceBound n).1
    · exact Filter.Eventually.of_forall fun n => (hVarianceBound n).2
    · simpa [Y] using hsecond
  exact ⟨hMean, hVariance⟩

end ProbabilityTheory

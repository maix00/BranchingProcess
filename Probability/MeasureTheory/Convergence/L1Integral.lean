/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integral convergence from `L¹` convergence

On a probability space, convergence of the `L¹` seminorm to a constant implies
convergence of the expectations. This is the expectation bridge used when a
Kingman limit is compared with finite-block means.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory

/-- If the `L¹` distance of integrable real-valued functions from a constant
tends to zero on a probability space, then their integrals tend to that
constant. -/
theorem tendsto_integral_of_eLpNorm_one_sub_const
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ℕ → Ω → ℝ) (c : ℝ)
    (hint : ∀ n, Integrable (f n) μ)
    (hL1 : Tendsto
      (fun n => eLpNorm (fun ω => f n ω - c) (1 : ℝ≥0∞) μ)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 c) := by
  have htoReal : Tendsto
      (fun n => (eLpNorm (fun ω => f n ω - c) (1 : ℝ≥0∞) μ).toReal)
      atTop (𝓝 0) := by
    change Tendsto (ENNReal.toReal ∘ fun n =>
      eLpNorm (fun ω => f n ω - c) (1 : ℝ≥0∞) μ) atTop (𝓝 0)
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1
  have hmeanBound (n : ℕ) :
      ‖(∫ ω, f n ω ∂μ) - c‖ ≤
        (eLpNorm (fun ω => f n ω - c) (1 : ℝ≥0∞) μ).toReal := by
    have hdiff : Integrable (fun ω => f n ω - c) μ :=
      (hint n).sub (integrable_const c)
    have hconst : (∫ _ω, c ∂μ) = c := by simp
    have hIntegral :
        (∫ ω, f n ω - c ∂μ) = (∫ ω, f n ω ∂μ) - c := by
      rw [integral_sub (hint n) (integrable_const c), hconst]
    rw [← hIntegral]
    calc
      ‖∫ ω, (f n ω - c) ∂μ‖ ≤ ∫ ω, ‖f n ω - c‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ = lpNorm (fun ω => f n ω - c) (1 : ℝ≥0∞) μ :=
        (lpNorm_one_eq_integral_norm hdiff.aestronglyMeasurable).symm
      _ = (eLpNorm (fun ω => f n ω - c) (1 : ℝ≥0∞) μ).toReal := by
        rw [toReal_eLpNorm]
  have hnorm : Tendsto
      (fun n => ‖(∫ ω, f n ω ∂μ) - c‖) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n => norm_nonneg _
    · exact Eventually.of_forall hmeanBound
    · exact htoReal
  have hdiff : Tendsto
      (fun n => (∫ ω, f n ω ∂μ) - c) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact hnorm
  have h := hdiff.add_const c
  have h' : Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 (0 + c)) :=
    h.congr' (Eventually.of_forall fun n => by ring)
  simpa using h'

end ProbabilityTheory

end

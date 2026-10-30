/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Moment bounds for finite sums

## Public declarations

- MeasureTheory.integral_pow_sum_le_of_uniform_moment_bound: for a finite
  index set s, nonnegative measurable functions Y i, and a natural number p,
  if each (p + 1)-st power is integrable and has integral at most C, then the
  sum is integrable to the same power and
  \[
    \int \left(\sum_{i\in s}Y_i\right)^{p+1}
      \le |s|^{p+1}C.
  \]

The proof combines Mathlib's finite-sum Jensen inequality
pow_sum_le_card_mul_sum_pow with linearity and monotonicity of the integral.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace MeasureTheory

/-- A uniform (p + 1)-st moment bound on nonnegative summands gives the
corresponding bound for their finite sum. -/
theorem integral_pow_sum_le_of_uniform_moment_bound
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (s : Finset ι)
    (p : ℕ) (Y : ι → Ω → ℝ)
    (hYmeas : ∀ i ∈ s, Measurable (Y i))
    (hYnonneg : ∀ i ∈ s, ∀ ω, 0 ≤ Y i ω)
    (C : ℝ)
    (hYintegrable : ∀ i ∈ s,
      Integrable (fun ω => (Y i ω) ^ (p + 1)) P)
    (hYmoment : ∀ i ∈ s,
      (∫ ω, (Y i ω) ^ (p + 1) ∂P) ≤ C) :
    Integrable (fun ω => (∑ i ∈ s, Y i ω) ^ (p + 1)) P ∧
      (∫ ω, (∑ i ∈ s, Y i ω) ^ (p + 1) ∂P) ≤
        (s.card : ℝ) ^ (p + 1) * C := by
  classical
  let F : Ω → ℝ := fun ω => ∑ i ∈ s, Y i ω
  let G : Ω → ℝ := fun ω =>
    (s.card : ℝ) ^ p * ∑ i ∈ s, (Y i ω) ^ (p + 1)
  have hFmeas : Measurable F := by
    dsimp [F]
    exact Finset.measurable_sum s (fun i hi => hYmeas i hi)
  have hsumPowIntegrable :
      Integrable (fun ω => ∑ i ∈ s, (Y i ω) ^ (p + 1)) P := by
    apply integrable_finsetSum s
    intro i hi
    exact hYintegrable i hi
  have hGintegrable : Integrable G P := by
    dsimp [G]
    exact hsumPowIntegrable.const_mul ((s.card : ℝ) ^ p)
  have hFnonneg (ω : Ω) : 0 ≤ F ω := by
    dsimp [F]
    apply Finset.sum_nonneg
    intro i hi
    exact hYnonneg i hi ω
  have hpointwise (ω : Ω) : F ω ^ (p + 1) ≤ G ω := by
    dsimp [F, G]
    exact pow_sum_le_card_mul_sum_pow
      (fun i hi => hYnonneg i hi ω) p
  have hFintegrable : Integrable (fun ω => F ω ^ (p + 1)) P := by
    apply hGintegrable.mono'
      (hFmeas.pow_const (p + 1)).aestronglyMeasurable
    filter_upwards [] with ω
    calc
      ‖F ω ^ (p + 1)‖ = F ω ^ (p + 1) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hFnonneg ω) _)]
      _ ≤ G ω := hpointwise ω
  have hIntegralBound :
      (∫ ω, F ω ^ (p + 1) ∂P) ≤ (s.card : ℝ) ^ (p + 1) * C := by
    calc
      (∫ ω, F ω ^ (p + 1) ∂P) ≤ ∫ ω, G ω ∂P :=
        integral_mono_ae hFintegrable hGintegrable
          (ae_of_all P hpointwise)
      _ = (s.card : ℝ) ^ p *
          ∑ i ∈ s, (∫ ω, (Y i ω) ^ (p + 1) ∂P) := by
        dsimp [G]
        rw [integral_const_mul,
          integral_finsetSum s (fun i hi => hYintegrable i hi)]
      _ ≤ (s.card : ℝ) ^ p * ((s.card : ℝ) * C) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          (∑ i ∈ s, (∫ ω, (Y i ω) ^ (p + 1) ∂P)) ≤
              ∑ i ∈ s, C := by
                exact Finset.sum_le_sum (fun i hi => hYmoment i hi)
          _ = (s.card : ℝ) * C := by simp
      _ = (s.card : ℝ) ^ (p + 1) * C := by
        rw [pow_succ]
        ring
  exact ⟨hFintegrable, by simpa [F] using hIntegralBound⟩

end MeasureTheory

end

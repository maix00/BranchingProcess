/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Independence.Integration

/-!
# Expectation bounds from an independent upper bound

This is a one-sided `L¹` estimate for splitting an expectation over an event
and its complement. On the exceptional event, the integrand is dominated by
an integrable upper-bound observable independent of that event.

## Public declarations

- `ProbabilityTheory.integral_le_of_eventwise_upper_bound_of_independent_upper_bound`:
  if $X\le z$ on $A^c$, $X\le Y$ on $A$, and $Y$ is integrable and independent
  of $\mathbf 1_A$, then
  $\int X\,d\mu\le z(1-\mu(A))+\mu(A)\int Y\,d\mu$.
- `ProbabilityTheory.integral_le_of_eventwise_upper_bound_of_independent_upper_bound_abs`:
  under the same hypotheses,
  $\int X\,d\mu\le z+\mu(A)(\int |Y|\,d\mu+|z|)$.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory

/-- If `X` is bounded above by `z` off `A` and by an independent integrable
upper-bound observable `Y` on `A`, then its expectation is bounded by the exact
event/complement split. -/
theorem integral_le_of_eventwise_upper_bound_of_independent_upper_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (A : Set Ω) (z : ℝ)
    (hA : MeasurableSet A)
    (hX : Integrable X μ) (hY : Integrable Y μ)
    (hIndependent : IndepFun Y (A.indicator (fun _ => (1 : ℝ))) μ)
    (hGood : ∀ ω ∉ A, X ω ≤ z)
    (hBad : ∀ ω ∈ A, X ω ≤ Y ω) :
    (∫ ω, X ω ∂μ) ≤
      z * (1 - μ.real A) + (∫ ω, Y ω ∂μ) * μ.real A := by
  let good : Ω → ℝ := Aᶜ.indicator (fun _ => (1 : ℝ))
  let bad : Ω → ℝ := A.indicator (fun _ => (1 : ℝ))
  have hGoodInt : Integrable good μ := by
    exact (integrable_const (1 : ℝ)).indicator hA.compl
  have hBadInt : Integrable bad μ := by
    exact (integrable_const (1 : ℝ)).indicator hA
  have hYBadInt : Integrable (fun ω => Y ω * bad ω) μ := by
    have hEq : (fun ω => Y ω * bad ω) = A.indicator Y := by
      funext ω
      by_cases hω : ω ∈ A <;> simp [bad, hω]
    rw [hEq]
    exact hY.indicator hA
  have hMajorInt : Integrable (fun ω => z * good ω + Y ω * bad ω) μ :=
    (hGoodInt.const_mul z).add hYBadInt
  have hPointwise : ∀ ω, X ω ≤ z * good ω + Y ω * bad ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simpa [good, bad, hω] using hBad ω hω
    · simpa [good, bad, hω] using hGood ω hω
  have hIntegral := integral_mono_ae hX hMajorInt (ae_of_all μ hPointwise)
  have hGoodIntegral : (∫ ω, good ω ∂μ) = μ.real Aᶜ := by
    simpa [good] using integral_indicator_const (1 : ℝ) hA.compl
  have hBadIntegral : (∫ ω, bad ω ∂μ) = μ.real A := by
    simpa [bad] using integral_indicator_const (1 : ℝ) hA
  have hFactor := hIndependent.integral_fun_mul_eq_mul_integral
    hY.aestronglyMeasurable hBadInt.aestronglyMeasurable
  have hFactorBad : (∫ ω, Y ω * bad ω ∂μ) =
      (∫ ω, Y ω ∂μ) * (∫ ω, bad ω ∂μ) := by
    simpa [bad] using hFactor
  calc
    (∫ ω, X ω ∂μ) ≤ ∫ ω, z * good ω + Y ω * bad ω ∂μ := hIntegral
    _ = z * (1 - μ.real A) + (∫ ω, Y ω ∂μ) * μ.real A := by
      rw [integral_add (hGoodInt.const_mul z) hYBadInt, integral_const_mul,
        hGoodIntegral, hFactorBad, hBadIntegral,
        MeasureTheory.probReal_compl_eq_one_sub hA]

/-- A convenient weaker form of the preceding estimate. It makes the error
nonnegative and is directly useful when separate bounds are available for the
event probability and the first moment of the upper-bound observable. -/
theorem integral_le_of_eventwise_upper_bound_of_independent_upper_bound_abs
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (A : Set Ω) (z : ℝ)
    (hA : MeasurableSet A)
    (hX : Integrable X μ) (hY : Integrable Y μ)
    (hIndependent : IndepFun Y (A.indicator (fun _ => (1 : ℝ))) μ)
    (hGood : ∀ ω ∉ A, X ω ≤ z)
    (hBad : ∀ ω ∈ A, X ω ≤ Y ω) :
    (∫ ω, X ω ∂μ) ≤
      z + μ.real A * ((∫ ω, |Y ω| ∂μ) + |z|) := by
  have hbase := integral_le_of_eventwise_upper_bound_of_independent_upper_bound
    μ X Y A z hA hX hY hIndependent hGood hBad
  have hp : 0 ≤ μ.real A := measureReal_nonneg
  have hYabs : (∫ ω, Y ω ∂μ) ≤ ∫ ω, |Y ω| ∂μ := by
    apply integral_mono_ae hY hY.abs
    exact ae_of_all μ fun ω => le_abs_self (Y ω)
  have hnegz : -z ≤ |z| := neg_le_abs z
  have hYmul := mul_le_mul_of_nonneg_left hYabs hp
  have hZmul := mul_le_mul_of_nonneg_left hnegz hp
  have hmul : z * (1 - μ.real A) + (∫ ω, Y ω ∂μ) * μ.real A ≤
      z + μ.real A * ((∫ ω, |Y ω| ∂μ) + |z|) := by
    nlinarith [hYmul, hZmul]
  exact hbase.trans hmul

end ProbabilityTheory

end

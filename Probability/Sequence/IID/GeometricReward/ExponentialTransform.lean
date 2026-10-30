/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.Independence.Integration

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.Independence.Basic
public import Probability.Sequence.IID.GeometricReward.Definitions

/-!
# Exponential transform of an IID failure cycle

## Public declarations

- `geometricFailureExponentialTerm` is the $n$th term: the first $n$ marks
  carry $e^{\theta Y}$ on failure and mark $n$ contributes the success event.
- `iidGeometricFailureExponentialTransform` states that if
  $p=\nu(B)$ and $A=\int e^{\theta Y}\mathbf 1_{B^c}\,d\nu$, then
  \[
    \mathbb E\!\left[\sum_{n\ge0}
      \mathrm{geometricFailureExponentialTerm}_n\right]
      = \frac{p}{1-A}
  \]
  as an equality in $[0,\infty]$, including the divergent case.

The proof factors each finite product by IID independence and sums the
resulting extended geometric series. Mathlib's `geometricMeasure` describes
the law of the number of failures; this marked-reward transform is a separate
identity. The reusable product-integral and geometric-series facts come from
Mathlib's `lintegral_prod_eq_prod_lintegral_of_indepFun` and
`ENNReal.tsum_geometric`.
-/

open MeasureTheory
open scoped BigOperators ENNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The `n`th term in the exponential expansion of a failure-only cycle:
each of the first `n` trials contributes the exponential weight on failure,
and trial `n` contributes the success indicator. -/
noncomputable def geometricFailureExponentialTerm
    (X : ℕ → Ω → α) (B : Set α) (Y : α → ℝ) (θ : ℝ) (n : ℕ) :
    Ω → ℝ≥0∞ :=
  fun ω => ∏ i ∈ Finset.range (n + 1),
    (if i < n then
      ENNReal.ofReal (Real.exp (θ * Y (X i ω))) *
        Bᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (X i ω)
    else B.indicator (fun _ => (1 : ℝ≥0∞)) (X i ω))

/-- Geometric exponential-transform identity for the failure-only cycle.
The left side sums over the disjoint events “the first success occurs at `n`”;
the first `n` marks carry `exp (θY)` only on failure, and the `n`th mark
contributes only the success indicator. Thus the numerator is the success
probability `p`, while the geometric ratio is
`A = ∫ exp (θY) 1_{Bᶜ} dν`.

The identity is stated in `ENNReal`, so Mathlib's extended geometric-series
formula covers both finite and infinite values without an `A < 1` hypothesis. -/
theorem iidGeometricFailureExponentialTransform
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → α) (hX : ∀ i, Measurable (X i))
    (hXi : iIndepFun X μ) (hLaw : ∀ i, μ.map (X i) = ν)
    (B : Set α) (hB : MeasurableSet B)
    (Y : α → ℝ) (hY : Measurable Y) (θ : ℝ)
    (p : ℝ≥0∞) (hprob : ν B = p)
    (A : ℝ≥0∞)
    (hA : ∫⁻ x, ENNReal.ofReal (Real.exp (θ * Y x)) *
      Bᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x ∂ν = A) :
    ∫⁻ ω, ∑' n, geometricFailureExponentialTerm X B Y θ n ω ∂μ =
      p / (1 - A) := by
  let failWeight : α → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (θ * Y x)) *
      Bᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x
  let successWeight : α → ℝ≥0∞ := fun x =>
    B.indicator (fun _ => (1 : ℝ≥0∞)) x
  have hfailMeas : Measurable failWeight := by
    dsimp [failWeight]
    exact (by fun_prop : Measurable fun x => ENNReal.ofReal (Real.exp (θ * Y x))).mul
      (measurable_const.indicator hB.compl)
  have hsuccessMeas : Measurable successWeight := by
    dsimp [successWeight]
    exact measurable_const.indicator hB
  have hfailMap (i : ℕ) :
      ∫⁻ ω, failWeight (X i ω) ∂μ = A := by
    rw [← lintegral_map hfailMeas (hX i), hLaw i]
    exact hA
  have hsuccessMap (i : ℕ) :
      ∫⁻ ω, successWeight (X i ω) ∂μ = p := by
    rw [← lintegral_map hsuccessMeas (hX i), hLaw i]
    rw [show successWeight = B.indicator (fun _ => (1 : ℝ≥0∞)) by rfl,
      lintegral_indicator_const hB]
    simp [hprob]
  have htermMeas (n : ℕ) :
      Measurable (geometricFailureExponentialTerm X B Y θ n) := by
    let factor : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      if i < n then failWeight (X i ω) else successWeight (X i ω)
    have hfactorMeas (i : ℕ) : Measurable (factor i) := by
      by_cases hi : i < n
      · simp [factor, hi]
        exact hfailMeas.comp (hX i)
      · simp [factor, hi]
        exact hsuccessMeas.comp (hX i)
    have hprodMeas (s : Finset ℕ) :
        Measurable (fun ω => ∏ i ∈ s, factor i ω) := by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        simp only [Finset.prod_insert hi]
        exact (hfactorMeas i).mul ih
    have htermEq : geometricFailureExponentialTerm X B Y θ n =
        fun ω => ∏ i ∈ Finset.range (n + 1), factor i ω := by
      funext ω
      unfold geometricFailureExponentialTerm
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hin : i < n
      · simp [factor, hin, failWeight]
      · have hlast : i = n := by
          have hi' := Finset.mem_range.mp hi
          omega
        subst i
        simp [factor, successWeight]
    rw [htermEq]
    exact hprodMeas _
  have htermIntegral (n : ℕ) :
      ∫⁻ ω, geometricFailureExponentialTerm X B Y θ n ω ∂μ = A ^ n * p := by
    let factor : ℕ → α → ℝ≥0∞ := fun i x =>
      if i < n then failWeight x else successWeight x
    have hfactorMeas : ∀ i, Measurable (factor i) := by
      intro i
      by_cases hi : i < n
      · simp [factor, hi]
        exact hfailMeas
      · simp [factor, hi]
        exact hsuccessMeas
    have hfactorInd : iIndepFun (fun i ω => factor i (X i ω)) μ :=
      hXi.comp factor hfactorMeas
    have hprod := lintegral_prod_eq_prod_lintegral_of_indepFun
      (Finset.range (n + 1)) (fun i ω => factor i (X i ω))
      hfactorInd (fun i => (hfactorMeas i).comp (hX i))
    have hfactorIntegral (i : ℕ) (hi : i < n) :
        ∫⁻ ω, factor i (X i ω) ∂μ = A := by
      simp [factor, hi, hfailMap]
    have hlastIntegral :
        ∫⁻ ω, factor n (X n ω) ∂μ = p := by
      simp [factor, hsuccessMap]
    have hprefix :
        (∏ i ∈ Finset.range n, ∫⁻ ω, factor i (X i ω) ∂μ) = A ^ n := by
      calc
        (∏ i ∈ Finset.range n, ∫⁻ ω, factor i (X i ω) ∂μ) =
            ∏ i ∈ Finset.range n, A := by
              apply Finset.prod_congr rfl
              intro i hi
              exact hfactorIntegral i (Finset.mem_range.mp hi)
        _ = A ^ n := by simp
    have htermEq : geometricFailureExponentialTerm X B Y θ n =
        fun ω => ∏ i ∈ Finset.range (n + 1), factor i (X i ω) := by
      funext ω
      unfold geometricFailureExponentialTerm
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hin : i < n
      · simp [factor, hin, failWeight]
      · have hlast : i = n := by
          have hi' := Finset.mem_range.mp hi
          omega
        subst i
        simp [factor, successWeight]
    rw [htermEq, hprod, Finset.prod_range_succ, hprefix, hlastIntegral]
  have hsum :
      ∫⁻ ω, ∑' n, geometricFailureExponentialTerm X B Y θ n ω ∂μ =
        ∑' n, (A ^ n * p) := by
    rw [lintegral_tsum (fun n => (htermMeas n).aemeasurable)]
    congr 1
    funext n
    exact htermIntegral n
  rw [hsum]
  calc
    ∑' n, (A ^ n * p) = ∑' n, (p * A ^ n) := by
      congr 1
      funext n
      exact mul_comm _ _
    _ = p * ∑' n, A ^ n := ENNReal.tsum_mul_left
    _ = p / (1 - A) := by rw [ENNReal.tsum_geometric]; simp [div_eq_mul_inv]

end ProbabilityTheory

end

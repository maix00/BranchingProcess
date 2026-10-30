/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.Integration

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.Independence.Basic
public import Probability.Sequence.IID.GeometricReward.Definitions
import all Probability.Sequence.IID.GeometricReward.Lemmas.FailurePrefix

/-!
# First moments of IID rewards before success

## Public declarations

- `iidGeometricReward_integral` gives the expected sum of a general reward over
  IID trials up to and including the first successful mark.
- `iidGeometricFailurePositiveReward_integral` gives the exact formula for a
  nonnegative reward supported on failures.
- `iidGeometricSplitCycle_integral` gives the exact signed first moment when
  failure and success marks contribute distinct rewards on the same trial.
- `iidGeometricSplitCycle_positiveReward_le` bounds the positive contribution
  of such a split cycle.

For success probability $p>0$, the base identity is
\[
  \mathbb E\!\left[\sum_{n\ge0}R(X_n)
    \mathbf 1_{\{X_i\notin B\;\forall i<n\}}\right]
  = \frac{1}{p}\int R\,d\nu.
\]
The mark on trial $n$ may determine whether that trial succeeds; independence
is used only between it and the preceding failure prefix. The proof uses
Mathlib's `iIndepFun.indepFun_finset`,
`IndepFun.integral_fun_mul_eq_mul_integral`, and
`tsum_geometric_of_lt_one`. The prefix-specific calculations are in
`Lemmas/FailurePrefix.lean`.
-/

open MeasureTheory
open scoped BigOperators ENNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

theorem iidGeometricReward_integral
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → α) (hX : ∀ i, Measurable (X i))
    (hXi : iIndepFun X μ) (hLaw : ∀ i, μ.map (X i) = ν)
    (B : Set α) (hB : MeasurableSet B)
    (R : α → ℝ) (hR : Measurable R) (hRi : Integrable R ν)
    (p : ℝ) (hp : 0 < p) (hprob : ν.real B = p) :
    ∫ ω, ∑' n, geometricPrefixRewardTerm X B R n ω ∂μ =
      (∫ x, R x ∂ν) / p := by
  have hq : ν.real Bᶜ = 1 - p := by
    rw [← hprob, measureReal_compl hB, probReal_univ]
  have hq_nonneg : 0 ≤ ν.real Bᶜ := measureReal_nonneg
  have hq_lt : ν.real Bᶜ < 1 := by
    rw [hq]
    linarith
  have hnormTerm (n : ℕ) :
      ∫ ω, |geometricPrefixRewardTerm X B R n ω| ∂μ =
        (∫ x, |R x| ∂ν) * (ν.real Bᶜ) ^ n := by
    have hAbsInt : Integrable (fun x => |R x|) ν := hRi.abs
    have hAbsMeas : Measurable fun x => |R x| := continuous_abs.measurable.comp hR
    have hterm := integral_geometricPrefixRewardTerm μ ν X hX hXi hLaw B hB
      (fun x => |R x|) hAbsMeas hAbsInt n
    have hpoint : (fun ω => |geometricPrefixRewardTerm X B R n ω|) =
        geometricPrefixRewardTerm X B (fun x => |R x|) n := by
      funext ω
      by_cases hω : ω ∈ geometricFailurePrefix X B n <;>
        simp [geometricPrefixRewardTerm, hω]
    rw [hpoint, hterm]
  have hsumNorm : Summable fun n =>
      ∫ ω, |geometricPrefixRewardTerm X B R n ω| ∂μ := by
    rw [show (fun n => ∫ ω,
      |geometricPrefixRewardTerm X B R n ω| ∂μ) =
        fun n => (∫ x, |R x| ∂ν) * (ν.real Bᶜ) ^ n by
          funext n; exact hnormTerm n]
    exact (summable_geometric_of_lt_one hq_nonneg hq_lt).mul_left _
  have htermsInt : ∀ n, Integrable (geometricPrefixRewardTerm X B R n) μ := by
    intro n
    have hprefixMeas := measurableSet_geometricFailurePrefix hX hB n
    have hprefixInt : Integrable
        ((geometricFailurePrefix X B n).indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hprefixMeas
    have hRcomp : Integrable (fun ω => R (X n ω)) μ :=
      (show Integrable R (μ.map (X n)) by rw [hLaw n]; exact hRi).comp_measurable (hX n)
    have hind := indep_geometricFailurePrefix_current μ X hX hXi B hB R hR n
    exact hind.integrable_mul hRcomp hprefixInt
  have hsum := integral_tsum_of_summable_integral_norm htermsInt hsumNorm
  rw [← hsum]
  rw [show (fun n => ∫ ω, geometricPrefixRewardTerm X B R n ω ∂μ) =
      fun n => (∫ x, R x ∂ν) * (ν.real Bᶜ) ^ n by
        funext n
        exact integral_geometricPrefixRewardTerm μ ν X hX hXi hLaw B hB R hR hRi n]
  have hgeom := tsum_geometric_of_lt_one hq_nonneg hq_lt
  rw [tsum_mul_left, hgeom, hq]
  field_simp [hp.ne']
  ring

/-- Exact first-moment formula for positive rewards accumulated only on
failed trials. The mark on a successful trial contributes zero. -/
theorem iidGeometricFailurePositiveReward_integral
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → α) (hX : ∀ i, Measurable (X i))
    (hXi : iIndepFun X μ) (hLaw : ∀ i, μ.map (X i) = ν)
    (B : Set α) (hB : MeasurableSet B)
    (Y : α → ℝ) (hY : Measurable Y)
    (hYint : Integrable (fun x => max (Y x) 0) ν)
    (p : ℝ) (hp : 0 < p) (hprob : ν.real B = p) :
    ∫ ω, ∑' n, geometricPrefixRewardTerm X B
      (fun x => max (Y x) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) x) n ω ∂μ =
      (∫ x, max (Y x) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) x ∂ν) / p := by
  have hRint : Integrable (fun x => max (Y x) 0 *
      Bᶜ.indicator (fun _ => (1 : ℝ)) x) ν := by
    have h := hYint.indicator hB.compl
    convert h using 1
    ext x
    by_cases hx : x ∈ B <;> simp [hx]
  have hRmeas : Measurable (fun x => max (Y x) 0 *
      Bᶜ.indicator (fun _ => (1 : ℝ)) x) :=
    (hY.max measurable_const).mul (measurable_const.indicator hB.compl)
  exact iidGeometricReward_integral μ ν X hX hXi hLaw B hB
    (fun x => max (Y x) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) x)
    hRmeas hRint p hp hprob

/-- A failure mark `Y` and a distinct success mark `Z` can occur on the same
trial. The expected signed full-cycle increment is the sum of their
event-restricted means, divided by the split probability. -/
theorem iidGeometricSplitCycle_integral
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → α) (hX : ∀ i, Measurable (X i))
    (hXi : iIndepFun X μ) (hLaw : ∀ i, μ.map (X i) = ν)
    (B : Set α) (hB : MeasurableSet B)
    (Y Z : α → ℝ) (hY : Measurable Y) (hZ : Measurable Z)
    (hYint : Integrable (fun x => Y x * Bᶜ.indicator (fun _ => (1 : ℝ)) x) ν)
    (hZint : Integrable (fun x => Z x * B.indicator (fun _ => (1 : ℝ)) x) ν)
    (p : ℝ) (hp : 0 < p) (hprob : ν.real B = p) :
    ∫ ω, ∑' n, geometricPrefixRewardTerm X B
      (fun x => Y x * Bᶜ.indicator (fun _ => (1 : ℝ)) x +
        Z x * B.indicator (fun _ => (1 : ℝ)) x) n ω ∂μ =
      ((∫ x, Y x * Bᶜ.indicator (fun _ => (1 : ℝ)) x ∂ν) +
        (∫ x, Z x * B.indicator (fun _ => (1 : ℝ)) x ∂ν)) / p := by
  have hRewardMeas : Measurable (fun x =>
      Y x * Bᶜ.indicator (fun _ => (1 : ℝ)) x +
        Z x * B.indicator (fun _ => (1 : ℝ)) x) :=
    (hY.mul (measurable_const.indicator hB.compl)).add
      (hZ.mul (measurable_const.indicator hB))
  calc
    ∫ ω, ∑' n, geometricPrefixRewardTerm X B
        (fun x => Y x * Bᶜ.indicator (fun _ => (1 : ℝ)) x +
          Z x * B.indicator (fun _ => (1 : ℝ)) x) n ω ∂μ =
      (∫ x, Y x * Bᶜ.indicator (fun _ => (1 : ℝ)) x +
        Z x * B.indicator (fun _ => (1 : ℝ)) x ∂ν) / p :=
          iidGeometricReward_integral μ ν X hX hXi hLaw B hB
            (fun x => Y x * Bᶜ.indicator (fun _ => (1 : ℝ)) x +
              Z x * B.indicator (fun _ => (1 : ℝ)) x) hRewardMeas
            (hYint.add hZint) p hp hprob
    _ = ((∫ x, Y x * Bᶜ.indicator (fun _ => (1 : ℝ)) x ∂ν) +
        (∫ x, Z x * B.indicator (fun _ => (1 : ℝ)) x ∂ν)) / p := by
          rw [integral_add hYint hZint]

/-- Nonnegative first-moment bound for the accumulated positive rewards in a
split cycle. Failed generations use the first-child mark `Y`, while a success
uses the distinct reserve mark `Z`. -/
theorem iidGeometricSplitCycle_positiveReward_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → α) (hX : ∀ i, Measurable (X i))
    (hXi : iIndepFun X μ) (hLaw : ∀ i, μ.map (X i) = ν)
    (B : Set α) (hB : MeasurableSet B)
    (Y Z : α → ℝ) (hY : Measurable Y) (hZ : Measurable Z)
    (hYint : Integrable (fun x => max (Y x) 0) ν)
    (hZint : Integrable (fun x => max (Z x) 0) ν)
    (p : ℝ) (hp : 0 < p) (hprob : ν.real B = p) :
    ∫ ω, ∑' n, geometricPrefixRewardTerm X B
      (fun x => max (Y x) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) x +
        max (Z x) 0 * B.indicator (fun _ => (1 : ℝ)) x) n ω ∂μ ≤
      ((∫ x, max (Y x) 0 ∂ν) + (∫ x, max (Z x) 0 *
        B.indicator (fun _ => (1 : ℝ)) x ∂ν)) / p := by
  have hYres : Integrable (fun x => max (Y x) 0 *
      Bᶜ.indicator (fun _ => (1 : ℝ)) x) ν := by
    have h := hYint.indicator hB.compl
    convert h using 1
    ext x
    by_cases hx : x ∈ B <;> simp [hx]
  have hZres : Integrable (fun x => max (Z x) 0 *
      B.indicator (fun _ => (1 : ℝ)) x) ν := by
    have h := hZint.indicator hB
    convert h using 1
    ext x
    by_cases hx : x ∈ B <;> simp [hx]
  have hRewardInt : Integrable (fun x =>
      max (Y x) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) x +
        max (Z x) 0 * B.indicator (fun _ => (1 : ℝ)) x) ν :=
    hYres.add hZres
  have hRewardMeas : Measurable (fun x =>
      max (Y x) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) x +
        max (Z x) 0 * B.indicator (fun _ => (1 : ℝ)) x) :=
    ((hY.max measurable_const).mul (measurable_const.indicator hB.compl)).add
      ((hZ.max measurable_const).mul (measurable_const.indicator hB))
  have hEq := iidGeometricReward_integral μ ν X hX hXi hLaw B hB
    (fun x => max (Y x) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) x +
      max (Z x) 0 * B.indicator (fun _ => (1 : ℝ)) x)
    hRewardMeas
    hRewardInt p hp hprob
  rw [hEq, integral_add hYres hZres]
  have hYbound :
      ∫ x, max (Y x) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) x ∂ν ≤
        ∫ x, max (Y x) 0 ∂ν := by
    apply integral_mono_ae hYres hYint
    filter_upwards [] with x
    by_cases hx : x ∈ B <;> simp [hx]
  have hnumerator :
      (∫ x, max (Y x) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) x ∂ν) +
          (∫ x, max (Z x) 0 * B.indicator (fun _ => (1 : ℝ)) x ∂ν) ≤
        (∫ x, max (Y x) 0 ∂ν) +
          (∫ x, max (Z x) 0 * B.indicator (fun _ => (1 : ℝ)) x ∂ν) :=
    add_le_add hYbound (le_refl _)
  exact (div_le_div_of_nonneg_right hnumerator hp.le)

end ProbabilityTheory

end

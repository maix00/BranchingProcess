/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Independence.Integration

/-!
# First-moment bounds for reserve rewards

An independent reserve continuation is often bounded by a deterministic
offset plus a finite sum of positive displacement increments.  This module
records the resulting `L¹` estimate using only integrability of the positive
parts.  It does not require integrability of the negative tails or mutual
independence among the reserve increments.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

/-- A deterministic nonnegative offset plus finitely many integrable positive
parts has exceptional-event expectation at most its first-moment bound times
the event probability, provided each summand is independent of the event.

This is the finite-sum form used for a pre-sampled reserve continuation.  The
independence assumptions are only termwise; the observables need not be
mutually independent. -/
theorem integral_const_add_finset_positivePart_indicator_le
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (s : Finset ι) (f : ι → Ω → ℝ) (E : Set Ω)
    (hpos : ∀ i ∈ s, Integrable (fun ω => max (f i ω) 0) μ)
    (hE : MeasurableSet E)
    (hind : ∀ i ∈ s,
      IndepFun (fun ω => max (f i ω) 0)
        (E.indicator (fun _ => (1 : ℝ))) μ)
    (C B p : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hmoment : (∑ i ∈ s, ∫ ω, max (f i ω) 0 ∂μ) ≤ B)
    (hprob : μ.real E ≤ p) :
    (∫ ω, (C + ∑ i ∈ s, max (f i ω) 0) *
        E.indicator (fun _ => (1 : ℝ)) ω ∂μ) ≤ (C + B) * p := by
  let reward : ι → Ω → ℝ := fun i ω => max (f i ω) 0
  let indicator : Ω → ℝ := E.indicator (fun _ => (1 : ℝ))
  have hsumInt : Integrable (fun ω => ∑ i ∈ s, reward i ω) μ :=
    integrable_finsetSum s (fun i hi => hpos i hi)
  have hsumInd : ∀ i ∈ s,
      IndepFun (fun ω => |reward i ω|) indicator μ := by
    intro i hi
    have h := (hind i hi).comp
      (by fun_prop : Measurable fun x : ℝ => |x|) measurable_id
    simpa [reward, indicator, Function.comp_def] using h
  have hsumFactor := ProbabilityTheory.integral_sum_abs_mul_indicator_eq
    μ s reward E (fun i hi => hpos i hi) hE hsumInd
  have hrewardAbs : ∀ i ω, |reward i ω| = reward i ω := by
    intro i ω
    exact abs_of_nonneg (le_max_right _ _)
  have hsumFactor' :
      (∫ ω, (∑ i ∈ s, reward i ω) * indicator ω ∂μ) =
        (∑ i ∈ s, ∫ ω, reward i ω ∂μ) * μ.real E := by
    simpa only [indicator, reward, hrewardAbs] using hsumFactor
  have hsumBound :
      (∫ ω, (∑ i ∈ s, reward i ω) * indicator ω ∂μ) ≤ B * μ.real E := by
    rw [hsumFactor']
    exact mul_le_mul_of_nonneg_right hmoment measureReal_nonneg
  have hconstFun :
      (fun ω => C * indicator ω) = E.indicator (fun _ => C) := by
    funext ω
    by_cases hω : ω ∈ E <;> simp [indicator, hω]
  have hconstInt :
      (∫ ω, C * indicator ω ∂μ) = C * μ.real E := by
    calc
      (∫ ω, C * indicator ω ∂μ) =
          ∫ ω, E.indicator (fun _ => C) ω ∂μ := by rw [hconstFun]
      _ = μ.real E • C := integral_indicator_const C hE
      _ = C * μ.real E := by rw [smul_eq_mul, mul_comm]
  have hsumFun :
      (fun ω => (∑ i ∈ s, reward i ω) * indicator ω) =
        E.indicator (fun ω => ∑ i ∈ s, reward i ω) := by
    funext ω
    by_cases hω : ω ∈ E <;> simp [indicator, hω]
  have hsumProductInt :
      Integrable (fun ω => (∑ i ∈ s, reward i ω) * indicator ω) μ := by
    rw [hsumFun]
    exact hsumInt.indicator hE
  have hconstProductInt : Integrable (fun ω => C * indicator ω) μ := by
    rw [hconstFun]
    exact (integrable_const C).indicator hE
  have htotalEq :
      (∫ ω, (C + ∑ i ∈ s, reward i ω) * indicator ω ∂μ) =
        C * μ.real E +
          ∫ ω, (∑ i ∈ s, reward i ω) * indicator ω ∂μ := by
    calc
      (∫ ω, (C + ∑ i ∈ s, reward i ω) * indicator ω ∂μ) =
          ∫ ω, (C * indicator ω +
            (∑ i ∈ s, reward i ω) * indicator ω) ∂μ := by
              rw [show (fun ω => (C + ∑ i ∈ s, reward i ω) * indicator ω) =
                fun ω => C * indicator ω +
                  (∑ i ∈ s, reward i ω) * indicator ω from by
                    funext ω
                    exact add_mul C _ _]
      _ = (∫ ω, C * indicator ω ∂μ) +
          ∫ ω, (∑ i ∈ s, reward i ω) * indicator ω ∂μ := by
            exact integral_add hconstProductInt hsumProductInt
      _ = C * μ.real E +
          ∫ ω, (∑ i ∈ s, reward i ω) * indicator ω ∂μ := by
            rw [hconstInt]
  have hOffsetMoment : 0 ≤ C + B := add_nonneg hC hB
  calc
    (∫ ω, (C + ∑ i ∈ s, reward i ω) * indicator ω ∂μ) =
        C * μ.real E +
          ∫ ω, (∑ i ∈ s, reward i ω) * indicator ω ∂μ := htotalEq
    _ ≤ C * μ.real E + B * μ.real E :=
      add_le_add (le_rfl) hsumBound
    _ = (C + B) * μ.real E := by ring
    _ ≤ (C + B) * p := mul_le_mul_of_nonneg_left hprob hOffsetMoment

end ProbabilityTheory.BranchingRandomWalk

end

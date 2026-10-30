/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Second-moment bounds for tails

## Public declarations

* `MeasureTheory.sq_mul_measureReal_abs_ge_le_tailIntegral` bounds
  $a^2\,\mu(|x|\geq a)$ by the second-moment integral on that tail, for
  $a\geq0$ and any measure on $\mathbb R$.
-/

open MeasureTheory

@[expose] public section

namespace MeasureTheory

/-- Markov's inequality for a nonnegative integrable function, written with
the real measure of its upper level set and the corresponding tail integral. -/
private theorem mul_measureReal_le_integral_indicator
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} (hf : Integrable f μ) (hf_nonneg : 0 ≤ f)
    (hf_meas : StronglyMeasurable f) (threshold : ℝ) :
    threshold * μ.real {x | threshold ≤ f x} ≤
      ∫ x, {x | threshold ≤ f x}.indicator f x ∂μ := by
  let tail : Set X := {x | threshold ≤ f x}
  have htail : MeasurableSet tail :=
    measurableSet_Ici.preimage hf_meas.measurable
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ.restrict tail) (f := f)
    (ae_restrict_of_forall_mem htail fun x _ => hf_nonneg x)
    (hf.mono_measure Measure.restrict_le_self) threshold
  change threshold * μ.real tail ≤ ∫ x, tail.indicator f x ∂μ
  rw [integral_indicator htail]
  change threshold * (μ.restrict tail).real tail ≤
    ∫ x in tail, f x ∂μ at hmarkov
  simpa only [Measure.real, Measure.restrict_apply htail,
    Set.inter_self] using hmarkov

/-- The second-moment tail integral bounds the squared threshold times the
real measure of the corresponding absolute-value tail. -/
theorem sq_mul_measureReal_abs_ge_le_tailIntegral
    (μ : Measure ℝ) (hsq : Integrable (fun x : ℝ => x ^ 2) μ)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    threshold ^ 2 * μ.real {x | threshold ≤ |x|} ≤
      ∫ x, {x | threshold ^ 2 ≤ x ^ 2}.indicator (fun x => x ^ 2) x ∂μ := by
  have h := mul_measureReal_le_integral_indicator hsq
    (fun x => sq_nonneg x) (by fun_prop) (threshold ^ 2)
  have hset : {x : ℝ | threshold ^ 2 ≤ x ^ 2} =
      {x | threshold ≤ |x|} := by
    ext x
    simpa only [Set.mem_ofPred_eq, sq_abs] using
      (sq_le_sq₀ hthreshold (abs_nonneg x))
  rw [← hset]
  exact h

end MeasureTheory

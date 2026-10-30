/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integrals over moving upper level sets

## Public declarations

* `MeasureTheory.tendsto_integral_indicator_of_threshold_tendsto_atTop` states
  that if $f\geq 0$ is integrable and $a_n\to+\infty$, then
  $\int 1_{\{a_n\leq f\}}f\,d\mu\to0$.
-/

open Filter MeasureTheory

@[expose] public section

namespace MeasureTheory

/-- The integral of an integrable nonnegative function over the part above a
threshold tends to zero as that threshold tends to infinity. -/
theorem tendsto_integral_indicator_of_threshold_tendsto_atTop
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} (hf : Integrable f μ) (hf_nonneg : 0 ≤ f)
    (threshold : ℕ → ℝ) (hthreshold : Tendsto threshold atTop atTop) :
    Tendsto (fun n : ℕ => ∫ x, {x | threshold n ≤ f x}.indicator f x ∂μ)
      atTop (nhds 0) := by
  have hmeas (n : ℕ) :
      AEStronglyMeasurable ({x | threshold n ≤ f x}.indicator f) μ := by
    exact hf.aestronglyMeasurable.indicator₀
      (hf.aemeasurable.nullMeasurable measurableSet_Ici)
  have hbound (n : ℕ) : ∀ᵐ x ∂μ,
      ‖{x | threshold n ≤ f x}.indicator f x‖ ≤ f x := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    by_cases hx : threshold n ≤ f x
    · rw [Set.indicator_of_mem (show x ∈ {y | threshold n ≤ f y} from hx),
        abs_of_nonneg (hf_nonneg x)]
    · rw [Set.indicator_of_notMem
          (show x ∉ {y | threshold n ≤ f y} from hx), abs_zero]
      exact hf_nonneg x
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => {x | threshold n ≤ f x}.indicator f x)
        atTop (nhds 0) := by
    filter_upwards [] with x
    have heventually' : ∀ᶠ n in atTop, f x + 1 ≤ threshold n :=
      tendsto_atTop.1 hthreshold (f x + 1)
    have heventually : ∀ᶠ n in atTop, f x < threshold n := by
      filter_upwards [heventually'] with n hn
      linarith
    apply tendsto_const_nhds.congr'
    filter_upwards [heventually] with n hn
    rw [Set.indicator_of_notMem]
    exact not_le_of_gt hn
  simpa using (tendsto_integral_of_dominated_convergence
    (f := fun _ : X => 0) f hmeas hf hbound hlim)

end MeasureTheory

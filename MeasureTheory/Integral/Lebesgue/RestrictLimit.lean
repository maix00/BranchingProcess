/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Limits of integrals over varying measurable sets

These lemmas use only a finite nonnegative integral and almost-everywhere
eventual exclusion from the sets.
-/

@[expose] public section

namespace MeasureTheory

open Filter
open scoped Topology

/-- The integral of an integrable nonnegative weight over a measurable set
tends to zero when almost every point eventually leaves the set. -/
theorem tendsto_lintegral_restrict_of_eventually_not_mem
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (weight : E → ENNReal) (band : ℕ → Set E)
    (hweight : Measurable weight)
    (hband : ∀ n, MeasurableSet (band n))
    (hfinite : (∫⁻ x, weight x ∂ν) ≠ ⊤)
    (haway : ∀ᵐ x ∂ν, ∀ᶠ n in atTop, x ∉ band n) :
    Tendsto (fun n => ∫⁻ x in band n, weight x ∂ν) atTop (𝓝 0) := by
  have hlim : ∀ᵐ x ∂ν,
      Tendsto (fun n => (band n).indicator weight x) atTop (𝓝 0) := by
    filter_upwards [haway] with x hx
    have heq : (fun n => (band n).indicator weight x) =ᶠ[atTop] fun _ => 0 := by
      filter_upwards [hx] with n hn
      exact Set.indicator_of_notMem hn _
    exact (tendsto_congr' heq).2 tendsto_const_nhds
  have hbound : ∀ n, (band n).indicator weight ≤ᵐ[ν] weight := by
    intro n
    filter_upwards [] with x
    by_cases hx : x ∈ band n
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have ht := tendsto_lintegral_of_dominated_convergence weight
    (fun n => (hweight.indicator (hband n))) hbound hfinite hlim
  simpa only [lintegral_indicator (hband _), lintegral_zero] using ht

/-- A sufficiently small restriction has integral below any prescribed
positive threshold. -/
theorem exists_lintegral_restrict_lt_of_eventually_not_mem
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (weight : E → ENNReal) (band : ℕ → Set E)
    (hweight : Measurable weight)
    (hband : ∀ n, MeasurableSet (band n))
    (hfinite : (∫⁻ x, weight x ∂ν) ≠ ⊤)
    (haway : ∀ᵐ x ∂ν, ∀ᶠ n in atTop, x ∉ band n)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ n, (∫⁻ x in band n, weight x ∂ν) < ENNReal.ofReal ρ := by
  have ht := tendsto_lintegral_restrict_of_eventually_not_mem ν weight band
    hweight hband hfinite haway
  have hpos : (0 : ENNReal) < ENNReal.ofReal ρ := ENNReal.ofReal_pos.mpr hρ
  exact ((tendsto_order.1 ht).2 _ hpos).exists

end MeasureTheory

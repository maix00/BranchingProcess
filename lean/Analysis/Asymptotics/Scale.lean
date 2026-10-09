/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Spatial scales below a reference normalization

This deterministic predicate isolates the scale relation shared by Gaussian
and stable small-deviation theorems.  The reference normalization is supplied
by the relevant domain-of-attraction theorem; no stability exponent or
specific probability law belongs in this layer.
-/

public section

open Filter

namespace Asymptotics

/-- A spatial scale diverges but is asymptotically negligible compared with a
reference normalization. -/
def IsSmallDeviationScale (scale normalization : ℕ → ℝ) : Prop :=
  Tendsto scale atTop atTop ∧
    Tendsto (fun n => scale n / normalization n) atTop (nhds 0)

namespace IsSmallDeviationScale

/-- Construct a small-deviation scale from its divergence and relative
vanishing limits. -/
theorem of_tendsto {scale normalization : ℕ → ℝ}
    (hscale : Tendsto scale atTop atTop)
    (hratio : Tendsto (fun n => scale n / normalization n) atTop (nhds 0)) :
    IsSmallDeviationScale scale normalization :=
  ⟨hscale, hratio⟩

theorem tendsto_atTop {scale normalization : ℕ → ℝ}
    (h : IsSmallDeviationScale scale normalization) :
    Tendsto scale atTop atTop := h.1

theorem tendsto_div {scale normalization : ℕ → ℝ}
    (h : IsSmallDeviationScale scale normalization) :
    Tendsto (fun n => scale n / normalization n) atTop (nhds 0) := h.2

theorem eventually_pos {scale normalization : ℕ → ℝ}
    (h : IsSmallDeviationScale scale normalization) :
    ∀ᶠ n in atTop, 0 < scale n :=
  h.tendsto_atTop.eventually (eventually_gt_atTop 0)

/-- Replacing a normalization by an asymptotically proportional positive
normalization preserves the small-deviation relation. -/
theorem of_tendsto_normalization_ratio
    {scale normalization normalization' : ℕ → ℝ} {c : ℝ}
    (h : IsSmallDeviationScale scale normalization)
    (hnormalization_pos : ∀ᶠ n in atTop, 0 < normalization n)
    (hratio : Tendsto (fun n => normalization' n / normalization n)
      atTop (nhds c)) (hc : 0 < c) :
    IsSmallDeviationScale scale normalization' := by
  have hratio_pos : ∀ᶠ n in atTop, 0 < normalization' n / normalization n :=
    hratio.eventually (Ioi_mem_nhds hc)
  have hnormalization'_pos : ∀ᶠ n in atTop, 0 < normalization' n := by
    filter_upwards [hnormalization_pos, hratio_pos] with n hn hr
    exact (div_pos_iff_of_pos_right hn).mp hr
  have hratio_small : Tendsto
      ((fun n => scale n / normalization n) /
        (fun n => normalization' n / normalization n)) atTop (nhds 0) := by
    simpa using h.tendsto_div.div hratio hc.ne'
  have hratio_eq : ((fun n => scale n / normalization n) /
      (fun n => normalization' n / normalization n)) =ᶠ[atTop]
      fun n => scale n / normalization' n := by
    filter_upwards [hnormalization_pos, hnormalization'_pos] with n hn hn'
    change (scale n / normalization n) /
      (normalization' n / normalization n) = scale n / normalization' n
    field_simp [ne_of_gt hn, ne_of_gt hn']
  exact ⟨h.tendsto_atTop, hratio_small.congr' hratio_eq⟩

/-- Rescaling a positive normalization by an eventual positive constant
preserves the small-deviation relation. -/
theorem of_eventually_const_mul {scale normalization normalization' : ℕ → ℝ}
    (h : IsSmallDeviationScale scale normalization)
    {c : ℝ} (hc : 0 < c)
    (hnormalization_pos : ∀ᶠ n in atTop, 0 < normalization n)
    (hnormalization : normalization' =ᶠ[atTop]
      fun n => c * normalization n) :
    IsSmallDeviationScale scale normalization' := by
  refine ⟨h.tendsto_atTop, ?_⟩
  have hratio : Tendsto (fun n => (scale n / normalization n) / c)
      atTop (nhds 0) := by
    simpa using h.tendsto_div.div_const c
  have heq : (fun n => (scale n / normalization n) / c) =ᶠ[atTop]
      fun n => scale n / normalization' n := by
    filter_upwards [hnormalization, hnormalization_pos] with n hnorm hpos
    rw [hnorm]
    field_simp [ne_of_gt hpos, ne_of_gt hc]
  exact hratio.congr' heq

end IsSmallDeviationScale

end Asymptotics

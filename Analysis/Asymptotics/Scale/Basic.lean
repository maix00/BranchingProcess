/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Real.Sqrt

/-!
# Spatial scales below a reference normalization

This deterministic predicate isolates the scale relation shared by Gaussian
and stable small-deviation theorems. The reference normalization is supplied
by the relevant domain-of-attraction theorem; no stability exponent or
specific probability law belongs in this layer.

## Public declarations

- `Asymptotics.IsSmallDeviationScale`: $a_n\to\infty$ and
  $a_n/b_n\to0$.
- `Asymptotics.IsSmallDeviationScale.of_tendsto`, `.tendsto_atTop`,
  `.tendsto_div`, and `.eventually_pos`: construct the predicate from its two
  limits and recover each limit or eventual positivity.
- `Asymptotics.IsSmallDeviationScale.eventually_lt_normalization`: if the
  reference normalization is eventually positive, then the spatial scale is
  eventually smaller than it.
- `Asymptotics.IsSmallDeviationScale.tendsto_pow_div_pow`: for $k>0$,
  $a_n^k/b_n^k\to0$.
- `Asymptotics.IsSmallDeviationScale.tendsto_normalization_div_scale_atTop`:
  if $b_n>0$ eventually, then $b_n/a_n\to\infty$.
- `Asymptotics.IsSmallDeviationScale.div_const`,
  `.of_tendsto_normalization_ratio`, and `.of_eventually_const_mul`: preserve
  the relation under fixed positive spatial rescaling and positive
  asymptotically proportional normalizations.
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

/-- A small-deviation scale is eventually smaller than its reference
normalization whenever that normalization is eventually positive. -/
theorem eventually_lt_normalization {scale normalization : ℕ → ℝ}
    (h : IsSmallDeviationScale scale normalization)
    (hnormalization : ∀ᶠ n in atTop, 0 < normalization n) :
    ∀ᶠ n in atTop, scale n < normalization n := by
  have hratio : ∀ᶠ n in atTop, scale n / normalization n < 1 :=
    (tendsto_order.1 h.tendsto_div).2 1 zero_lt_one
  filter_upwards [hnormalization, hratio] with n hn hratio
  exact (div_lt_one hn).mp hratio

/-- Raising the relative scale to any natural power preserves convergence to
zero, expressed as the corresponding ratio of powers. -/
theorem tendsto_pow_div_pow {scale normalization : ℕ → ℝ}
    (h : IsSmallDeviationScale scale normalization) (power : ℕ)
    (hpower : 0 < power) :
    Tendsto (fun n => scale n ^ power / normalization n ^ power)
      atTop (nhds 0) := by
  simpa [div_pow, Nat.ne_of_gt hpower] using h.tendsto_div.pow power

/-- If the normalization is eventually positive, it dominates the
small-deviation scale by a ratio tending to infinity. -/
theorem tendsto_normalization_div_scale_atTop
    {scale normalization : ℕ → ℝ}
    (h : IsSmallDeviationScale scale normalization)
    (hnormalization : ∀ᶠ n in atTop, 0 < normalization n) :
    Tendsto (fun n => normalization n / scale n) atTop atTop := by
  have hratio_pos : ∀ᶠ n in atTop, 0 < scale n / normalization n := by
    filter_upwards [hnormalization, h.eventually_pos] with n hn hs
    exact div_pos hs hn
  have hratio_within : Tendsto (fun n => scale n / normalization n)
      atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨h.tendsto_div, hratio_pos⟩
  have hinv : Tendsto (fun n => (scale n / normalization n)⁻¹)
      atTop atTop := tendsto_inv_nhdsGT_zero.comp hratio_within
  have heq : (fun n => (scale n / normalization n)⁻¹) =ᶠ[atTop]
      fun n => normalization n / scale n := by
    filter_upwards [hnormalization, h.eventually_pos] with n hn hs
    field_simp [hn.ne', hs.ne']
  exact hinv.congr' heq

end IsSmallDeviationScale

namespace IsSmallDeviationScale

/-- Dividing a small-deviation scale by a fixed positive spatial factor
preserves its relation to the reference normalization. -/
theorem div_const {scale normalization : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : IsSmallDeviationScale scale normalization) :
    IsSmallDeviationScale (fun n => scale n / c) normalization := by
  refine ⟨?_, ?_⟩
  · apply Filter.tendsto_atTop_atTop.2
    intro b
    obtain ⟨N, hN⟩ :=
      (Filter.tendsto_atTop_atTop.1 h.tendsto_atTop) (b * c)
    refine ⟨N, ?_⟩
    intro n hn
    apply (le_div_iff₀ hc).2
    exact hN n hn
  · have hratio : Tendsto (fun n => (scale n / normalization n) / c)
        atTop (nhds 0) := by
      simpa using h.tendsto_div.div_const c
    have heq : (fun n => (scale n / c) / normalization n) =ᶠ[atTop]
        fun n => (scale n / normalization n) / c := by
      filter_upwards [] with n
      simp only [div_div]
      rw [mul_comm c (normalization n)]
    exact hratio.congr' heq.symm

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

/-- If a small-deviation scale is negligible compared with `sqrt n`, its
square divided by `n` tends to zero. -/
theorem tendsto_sq_div_natCast_zero {scale : ℕ → ℝ}
    (h : IsSmallDeviationScale scale (fun n => Real.sqrt n)) :
    Tendsto (fun n => scale n ^ 2 / (n : ℝ)) atTop (nhds 0) := by
  have hpow := h.tendsto_pow_div_pow 2 (by norm_num)
  apply hpow.congr'
  filter_upwards [] with n
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]

/-- If a small-deviation scale is negligible compared with `sqrt n`, the
number of its squared spatial blocks available by time `n` tends to infinity.
-/
theorem tendsto_natCast_div_sq_atTop {scale : ℕ → ℝ}
    (h : IsSmallDeviationScale scale (fun n => Real.sqrt n)) :
    Tendsto (fun n : ℕ => (n : ℝ) / scale n ^ 2) atTop atTop := by
  have hnormalization_pos :
      ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hroot := h.tendsto_normalization_div_scale_atTop hnormalization_pos
  have hmul := hroot.atTop_mul_atTop₀ hroot
  apply hmul.congr'
  filter_upwards [] with n
  rw [← pow_two, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

end IsSmallDeviationScale

end Asymptotics

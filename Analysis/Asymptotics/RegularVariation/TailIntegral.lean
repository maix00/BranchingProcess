/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Analysis.Asymptotics.RegularVariation.Integral
public import Analysis.Asymptotics.RegularVariation.MonotoneDensity
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Regular variation of integrated monotone tails

For a nonnegative antitone function, regular variation of its tail is
equivalent to regular variation of its twice-integrated tail. The forward
direction uses Karamata's integral theorem; the reverse direction applies the
monotone density theorem twice, with `s = t ^ 2` handling the factor `t` in the
first integral.
-/

open Filter MeasureTheory Set

@[expose] public section

namespace Asymptotics

/-- The first integrated tail, with its natural zero extension to negative
arguments. -/
noncomputable def firstTailIntegral (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..max x 0, t * H t

/-- The second integrated tail associated with `firstTailIntegral`. -/
noncomputable def secondTailIntegral (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..x, firstTailIntegral H t

/-- A regularly varying nonnegative antitone tail of index `-α` has a first
integrated tail asymptotic to `x² H(x) / (2 - α)`. The substitution `s = t²`
reduces the weighted integral to the ordinary antitone Karamata theorem. -/
theorem IsRegularlyVaryingAtTop.tendsto_firstTailIntegral_div_mul
    {H : ℝ → ℝ} {α : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hreg : IsRegularlyVaryingAtTop H (-α))
    (hanti : Antitone H)
    (hHnonneg : ∀ x, 0 ≤ H x)
    (hHleOne : ∀ ⦃x : ℝ⦄, 0 ≤ x → H x ≤ 1) :
    Tendsto (fun x : ℝ => firstTailIntegral H x / (x ^ 2 * H x)) atTop
      (nhds (1 / (2 - α))) := by
  let G : ℝ → ℝ := fun y => H (Real.sqrt y)
  let J : ℝ → ℝ := fun y => ∫ s in (0:ℝ)..y, G s
  have hGreg : IsRegularlyVaryingAtTop G (-(α / 2)) := by
    have h := hreg.comp_rpow (by norm_num : (0:ℝ) < (1:ℝ) / 2)
    simpa [G, Real.sqrt_eq_rpow, div_eq_mul_inv, mul_comm, mul_left_comm,
      mul_assoc] using h
  have hGanti : Antitone G := by
    intro x y hxy
    exact hanti (Real.sqrt_le_sqrt hxy)
  have hGnonneg : ∀ ⦃y : ℝ⦄, 0 ≤ y → 0 ≤ G y := by
    intro y hy
    exact hHnonneg _
  have hGleOne : ∀ ⦃y : ℝ⦄, 0 ≤ y → G y ≤ 1 := by
    intro y hy
    exact hHleOne (Real.sqrt_nonneg y)
  have hGpos : ∀ᶠ y : ℝ in atTop, 0 < G y :=
    Real.tendsto_sqrt_atTop.eventually hreg.eventually_pos
  have hJratio := hGreg.tendsto_intervalIntegral_div_mul_of_antitone
    (by positivity : 0 ≤ α / 2) (by nlinarith : α / 2 < 1)
    hGanti hGnonneg hGleOne
  have hJratioSq : Tendsto
      (fun x : ℝ => J (x ^ 2) / (x ^ 2 * G (x ^ 2))) atTop
      (nhds (1 / (1 - α / 2))) := by
    change Tendsto (fun x : ℝ =>
      (∫ s in (0:ℝ)..x ^ 2, G s) / (x ^ 2 * G (x ^ 2))) atTop _
    exact hJratio.comp (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0))
  have hJchange (y : ℝ) (hy : 0 ≤ y) :
      J y = 2 * firstTailIntegral H (Real.sqrt y) := by
    have hsqrt : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
    have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0:ℝ)) (b := Real.sqrt y)
      (f := fun t : ℝ => t ^ 2) (f' := fun t => 2*t)
      (g := fun s : ℝ => H (Real.sqrt s))
      (by fun_prop)
      (by
        intro t ht
        simpa using hasDerivAt_pow 2 t)
      (by
        intro t ht
        have ht0 : 0 < t := by
          simpa [min_eq_left hsqrt, max_eq_right hsqrt] using ht.1
        exact mul_nonneg (by norm_num) ht0.le)
    have hleft : (∫ t in (0:ℝ)..Real.sqrt y,
        (fun s : ℝ => H (Real.sqrt s)) (t ^ 2) * (2*t)) =
        2 * firstTailIntegral H (Real.sqrt y) := by
      have heq : EqOn
          (fun t : ℝ => H (Real.sqrt (t ^ 2)) * (2*t))
          (fun t => 2 * (t * H t)) (uIcc 0 (Real.sqrt y)) := by
        intro t ht
        have ht0 : 0 ≤ t := by
          simpa [uIcc_of_le hsqrt] using ht.1
        change H (Real.sqrt (t ^ 2)) * (2*t) = 2 * (t * H t)
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht0]
        ring
      calc
        (∫ t in (0:ℝ)..Real.sqrt y,
            (fun s : ℝ => H (Real.sqrt s)) (t ^ 2) * (2*t))
            = ∫ t in (0:ℝ)..Real.sqrt y, 2 * (t * H t) :=
              intervalIntegral.integral_congr heq
        _ = 2 * firstTailIntegral H (Real.sqrt y) := by
          rw [intervalIntegral.integral_const_mul]
          simp [firstTailIntegral]
    calc
      J y = ∫ t in (0:ℝ)..Real.sqrt y,
          (fun s : ℝ => H (Real.sqrt s)) (t ^ 2) * (2*t) := by
            dsimp [J, G]
            have hsub' : (∫ t in (0:ℝ)..Real.sqrt y,
                (fun s : ℝ => H (Real.sqrt s)) (t ^ 2) * (2*t)) =
                ∫ u in (0:ℝ)..y, H (Real.sqrt u) := by
              simpa [hsq] using hsub
            exact hsub'.symm
      _ = 2 * firstTailIntegral H (Real.sqrt y) := hleft
  have hratio : Tendsto
      (fun x : ℝ => firstTailIntegral H x / (x ^ 2 * H x)) atTop
      (nhds (1 / (2 - α))) := by
    have hscale := hJratioSq.const_mul (1 / 2 : ℝ)
    have hconst : (1 / 2 : ℝ) * (1 / (1 - α / 2)) = 1 / (2 - α) := by
      have hden : 1 - α / 2 ≠ 0 := by linarith
      field_simp
    rw [hconst] at hscale
    have heq : (fun x : ℝ => (1 / 2 : ℝ) *
        (J (x ^ 2) / (x ^ 2 * G (x ^ 2)))) =ᶠ[atTop]
        fun x => firstTailIntegral H x / (x ^ 2 * H x) := by
      filter_upwards [eventually_gt_atTop (0:ℝ), hreg.eventually_pos] with x hx hxH
      have hchange := hJchange (x ^ 2) (sq_nonneg x)
      have hsqrt : Real.sqrt (x ^ 2) = x := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hx]
      simp only [hsqrt] at hchange
      dsimp [G]
      rw [hchange, Real.sqrt_sq_eq_abs, abs_of_pos hx]
      field_simp [ne_of_gt hx, ne_of_gt hxH]
    exact hscale.congr' heq
  exact hratio

/-- If `H` is a bounded nonnegative antitone regularly varying tail of index
`-α`, then its first integrated tail is regularly varying with index `2 - α`.
-/
theorem IsRegularlyVaryingAtTop.isRegularlyVaryingAtTop_firstTailIntegral
    {H : ℝ → ℝ} {α : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hreg : IsRegularlyVaryingAtTop H (-α))
    (hanti : Antitone H)
    (hHnonneg : ∀ x, 0 ≤ H x)
    (hHleOne : ∀ ⦃x : ℝ⦄, 0 ≤ x → H x ≤ 1) :
    IsRegularlyVaryingAtTop (firstTailIntegral H) (2 - α) := by
  have hratio := hreg.tendsto_firstTailIntegral_div_mul hα₀ hα₂ hanti
    hHnonneg hHleOne
  have hpowEq : (fun x : ℝ => x ^ (2:ℝ)) =ᶠ[atTop] fun x => x ^ 2 := by
    filter_upwards [] with x
    exact Real.rpow_natCast x 2
  have hpow : IsRegularlyVaryingAtTop (fun x : ℝ => x ^ 2) 2 := by
    exact (IsRegularlyVaryingAtTop.rpow (2:ℝ)).congr hpowEq
  have hden : IsRegularlyVaryingAtTop
      (fun x : ℝ => x ^ 2 * H x) (2 - α) := by
    have h := hpow.mul hreg
    simpa [sub_eq_add_neg] using h
  have hlimpos : 0 < 1 / (2 - α) := by
    positivity
  have hratioSlow : IsSlowlyVaryingAtTop
      (fun x : ℝ => firstTailIntegral H x / (x ^ 2 * H x)) :=
    IsSlowlyVaryingAtTop.of_tendsto_pos
      (f := fun x : ℝ => firstTailIntegral H x / (x ^ 2 * H x)) hlimpos hratio
  have hmul := IsRegularlyVaryingAtTop.mul hratioSlow hden
  have heq : (fun x : ℝ =>
      (firstTailIntegral H x / (x ^ 2 * H x)) * (x ^ 2 * H x)) =ᶠ[atTop]
      firstTailIntegral H := by
    filter_upwards [eventually_gt_atTop (0:ℝ), hreg.eventually_pos] with x hx hHx
    have hdenpos : 0 < x ^ 2 * H x := mul_pos (sq_pos_of_pos hx) hHx
    simp [ne_of_gt hdenpos]
  have hrv : IsRegularlyVaryingAtTop
      (fun x : ℝ => firstTailIntegral H x) (2 - α) := by
    convert hmul.congr heq using 1
    ring
  exact hrv

/-- A bounded nonnegative antitone regularly varying tail of index `-α` has
twice-integrated tail regularly varying with index `3 - α`. -/
theorem IsRegularlyVaryingAtTop.isRegularlyVaryingAtTop_secondTailIntegral
    {H : ℝ → ℝ} {α : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hreg : IsRegularlyVaryingAtTop H (-α))
    (hanti : Antitone H)
    (hHnonneg : ∀ x, 0 ≤ H x)
    (hHleOne : ∀ ⦃x : ℝ⦄, 0 ≤ x → H x ≤ 1)
    (hHint : ∀ a b : ℝ,
      IntervalIntegrable (fun t : ℝ => t * H t) volume a b) :
    IsRegularlyVaryingAtTop (secondTailIntegral H) (3 - α) := by
  let H₁ : ℝ → ℝ := firstTailIntegral H
  have hH₁nonneg : ∀ x, 0 ≤ H₁ x := by
    intro x
    by_cases hx : x < 0
    · simp [H₁, firstTailIntegral, max_eq_right (le_of_lt hx)]
    · have hx0 : 0 ≤ x := le_of_not_gt hx
      change 0 ≤ ∫ t in (0:ℝ)..max x 0, t * H t
      rw [max_eq_left hx0]
      apply intervalIntegral.integral_nonneg hx0
      intro t ht
      exact mul_nonneg ht.1 (hHnonneg t)
  have hH₁mono : Monotone H₁ := by
    intro x y hxy
    let a : ℝ := max x 0
    let b : ℝ := max y 0
    have hab : a ≤ b := max_le_max_right 0 hxy
    have h0a : 0 ≤ a := le_max_right x 0
    have hnonnegInt : 0 ≤ ∫ t in a..b, t * H t := by
      apply intervalIntegral.integral_nonneg hab
      intro t ht
      exact mul_nonneg (le_trans h0a ht.1) (hHnonneg t)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hHint 0 a) (hHint a b)
    have hEq : H₁ y = H₁ x + ∫ t in a..b, t * H t := by
      dsimp [H₁, firstTailIntegral, a, b]
      exact hadd.symm
    rw [hEq]
    linarith
  have hH₁int : ∀ a b : ℝ, IntervalIntegrable H₁ volume a b :=
    fun a b => hH₁mono.intervalIntegrable
  have hH₁reg := hreg.isRegularlyVaryingAtTop_firstTailIntegral
    hα₀ hα₂ hanti hHnonneg hHleOne
  have hratio := hH₁reg.tendsto_intervalIntegral_div_mul_of_monotone
    (by linarith : -1 < 2 - α) hH₁mono hH₁nonneg
  have hratio' : Tendsto (fun x : ℝ =>
      secondTailIntegral H x / (x * H₁ x)) atTop
      (nhds (1 / (3 - α))) := by
    have heq : (fun x : ℝ =>
        secondTailIntegral H x / (x * H₁ x)) =ᶠ[atTop]
        fun x => (∫ t in (0:ℝ)..x, H₁ t) / (x * H₁ x) := by
      filter_upwards [] with x
      rfl
    have hlim := hratio.congr' heq.symm
    have hconst : (2 - α) + 1 = 3 - α := by ring
    simpa [hconst] using hlim
  have hscaleEq : (fun x : ℝ => x ^ (1:ℝ)) =ᶠ[atTop] fun x => x := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [Real.rpow_one]
  have hpow : IsRegularlyVaryingAtTop (fun x : ℝ => x) 1 :=
    (IsRegularlyVaryingAtTop.rpow (1:ℝ)).congr hscaleEq
  have hscale : IsRegularlyVaryingAtTop (fun x : ℝ => x * H₁ x) (3 - α) := by
    have h := hpow.mul hH₁reg
    have hindex : 1 + (2 - α) = 3 - α := by ring
    simpa [H₁, hindex] using h
  have hlimpos : 0 < 1 / (3 - α) := one_div_pos.mpr (by linarith : 0 < 3 - α)
  have hratioSlow : IsSlowlyVaryingAtTop
      (fun x : ℝ => secondTailIntegral H x / (x * H₁ x)) :=
    IsSlowlyVaryingAtTop.of_tendsto_pos hlimpos hratio'
  have hmul := IsRegularlyVaryingAtTop.mul hratioSlow hscale
  have heq : (fun x : ℝ =>
      (secondTailIntegral H x / (x * H₁ x)) * (x * H₁ x)) =ᶠ[atTop]
      secondTailIntegral H := by
    filter_upwards [eventually_gt_atTop (0:ℝ), hH₁reg.eventually_pos] with x hx hHx
    have hdenpos : 0 < x * H₁ x := mul_pos hx hHx
    simp [ne_of_gt hdenpos]
  convert hmul.congr heq using 1
  ring

/-- For a nonnegative antitone regularly varying tail, the second integrated
tail has its exact Karamata ratio. This combines the first- and second-stage
integral ratios, reusing Mathlib's monotone integral theorem at each stage. -/
theorem IsRegularlyVaryingAtTop.tendsto_secondTailIntegral_div_mul
    {H : ℝ → ℝ} {α : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hreg : IsRegularlyVaryingAtTop H (-α))
    (hanti : Antitone H)
    (hHnonneg : ∀ x, 0 ≤ H x)
    (hHleOne : ∀ ⦃x : ℝ⦄, 0 ≤ x → H x ≤ 1)
    (hHint : ∀ a b : ℝ,
      IntervalIntegrable (fun t : ℝ => t * H t) volume a b) :
    Tendsto (fun x : ℝ => secondTailIntegral H x / (x ^ 3 * H x)) atTop
      (nhds (1 / ((2 - α) * (3 - α)))) := by
  let H₁ : ℝ → ℝ := firstTailIntegral H
  have hH₁nonneg : ∀ x, 0 ≤ H₁ x := by
    intro x
    by_cases hx : x < 0
    · simp [H₁, firstTailIntegral, max_eq_right (le_of_lt hx)]
    · have hx0 : 0 ≤ x := le_of_not_gt hx
      change 0 ≤ ∫ t in (0:ℝ)..max x 0, t * H t
      rw [max_eq_left hx0]
      apply intervalIntegral.integral_nonneg hx0
      intro t ht
      exact mul_nonneg ht.1 (hHnonneg t)
  have hH₁mono : Monotone H₁ := by
    intro x y hxy
    let a : ℝ := max x 0
    let b : ℝ := max y 0
    have hab : a ≤ b := max_le_max_right 0 hxy
    have h0a : 0 ≤ a := le_max_right x 0
    have hnonnegInt : 0 ≤ ∫ t in a..b, t * H t := by
      apply intervalIntegral.integral_nonneg hab
      intro t ht
      exact mul_nonneg (le_trans h0a ht.1) (hHnonneg t)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hHint 0 a) (hHint a b)
    have hEq : H₁ y = H₁ x + ∫ t in a..b, t * H t := by
      dsimp [H₁, firstTailIntegral, a, b]
      exact hadd.symm
    rw [hEq]
    linarith
  have hH₁int : ∀ a b : ℝ, IntervalIntegrable H₁ volume a b :=
    fun a b => hH₁mono.intervalIntegrable
  have hH₁reg := hreg.isRegularlyVaryingAtTop_firstTailIntegral
    hα₀ hα₂ hanti hHnonneg hHleOne
  have hratio₂ : Tendsto
      (fun x : ℝ => secondTailIntegral H x / (x * H₁ x)) atTop
      (nhds (1 / (3 - α))) := by
    have hratio := hH₁reg.tendsto_intervalIntegral_div_mul_of_monotone
      (by linarith : -1 < 2 - α) hH₁mono hH₁nonneg
    have heq : (fun x : ℝ => secondTailIntegral H x / (x * H₁ x)) =ᶠ[atTop]
        fun x => (∫ t in (0:ℝ)..x, H₁ t) / (x * H₁ x) := by
      filter_upwards [] with x
      rfl
    have hlim := hratio.congr' heq.symm
    have hconst : (2 - α) + 1 = 3 - α := by ring
    simpa [hconst] using hlim
  have hratio₁ := hreg.tendsto_firstTailIntegral_div_mul
    hα₀ hα₂ hanti hHnonneg hHleOne
  have hprod := hratio₂.mul hratio₁
  have hEq : (fun x : ℝ =>
      (secondTailIntegral H x / (x * H₁ x)) *
        (H₁ x / (x ^ 2 * H x))) =ᶠ[atTop]
      fun x => secondTailIntegral H x / (x ^ 3 * H x) := by
    filter_upwards [eventually_gt_atTop (0:ℝ), hH₁reg.eventually_pos,
      hreg.eventually_pos] with x hx hH₁x hHx
    dsimp [H₁]
    field_simp [ne_of_gt hx, ne_of_gt hH₁x, ne_of_gt hHx]
  have hconst : (1 / (3 - α)) * (1 / (2 - α)) =
      1 / ((2 - α) * (3 - α)) := by
    have h₂ : 2 - α ≠ 0 := ne_of_gt (by linarith)
    have h₃ : 3 - α ≠ 0 := ne_of_gt (by linarith)
    field_simp
  have hfinal : Tendsto (fun x : ℝ => secondTailIntegral H x /
      (x ^ 3 * H x)) atTop
      (nhds ((1 / (3 - α)) * (1 / (2 - α)))) := hprod.congr' hEq
  rw [hconst] at hfinal
  exact hfinal

/-- If the second integrated tail has positive index `ρ + 1`, then the original
nonnegative antitone tail is regularly varying with index `ρ - 2`. -/
theorem IsRegularlyVaryingAtTop.of_secondTailIntegral
    {H : ℝ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hanti : Antitone H)
    (hHnonneg : ∀ x, 0 ≤ H x)
    (hHint : ∀ a b : ℝ,
      IntervalIntegrable (fun t : ℝ => t * H t) volume a b)
    (hSecond : IsRegularlyVaryingAtTop (secondTailIntegral H) (ρ + 1)) :
    IsRegularlyVaryingAtTop H (ρ - 2) := by
  let H₁ : ℝ → ℝ := firstTailIntegral H
  let G : ℝ → ℝ := fun y => H (Real.sqrt y)
  have hH₁nonneg : ∀ x, 0 ≤ H₁ x := by
    intro x
    by_cases hx : x < 0
    · simp [H₁, firstTailIntegral, max_eq_right (le_of_lt hx)]
    · have hx0 : 0 ≤ x := le_of_not_gt hx
      change 0 ≤ ∫ t in (0:ℝ)..max x 0, t * H t
      rw [max_eq_left hx0]
      apply intervalIntegral.integral_nonneg hx0
      intro t ht
      exact mul_nonneg ht.1 (hHnonneg t)
  have hH₁mono : Monotone H₁ := by
    intro x y hxy
    let a : ℝ := max x 0
    let b : ℝ := max y 0
    have hab : a ≤ b := max_le_max_right 0 hxy
    have h0a : 0 ≤ a := le_max_right x 0
    have h0b : 0 ≤ b := le_max_right y 0
    have hnonnegInt : 0 ≤ ∫ t in a..b, t * H t := by
      apply intervalIntegral.integral_nonneg hab
      intro t ht
      exact mul_nonneg (le_trans h0a ht.1) (hHnonneg t)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hHint 0 a) (hHint a b)
    have hEq : H₁ y = H₁ x + ∫ t in a..b, t * H t := by
      dsimp [H₁, firstTailIntegral, a, b]
      exact hadd.symm
    rw [hEq]
    linarith
  have hH₁int : ∀ a b : ℝ, IntervalIntegrable H₁ volume a b :=
    fun a b => hH₁mono.intervalIntegrable
  have hH₁pos : ∀ᶠ x : ℝ in atTop, 0 < H₁ x := by
    have hSecondPos := hSecond.eventually_pos
    filter_upwards [hSecondPos, eventually_gt_atTop (0:ℝ)] with x hxSecond hx
    by_contra hnot
    have hxZero : H₁ x = 0 := le_antisymm (le_of_not_gt hnot) (hH₁nonneg x)
    have hzeroOn : EqOn H₁ (fun _ : ℝ => 0) (uIcc 0 x) := by
      intro t ht
      rw [uIcc_of_le hx.le] at ht
      have hle : H₁ t ≤ H₁ x := hH₁mono ht.2
      have hnonneg := hH₁nonneg t
      rw [hxZero] at hle
      linarith
    have hzeroInt : (∫ t in (0:ℝ)..x, H₁ t) = 0 := by
      rw [intervalIntegral.integral_congr hzeroOn]
      simp
    dsimp [secondTailIntegral, H₁] at hxSecond ⊢
    rw [hzeroInt] at hxSecond
    linarith
  have hH₁reg : IsRegularlyVaryingAtTop H₁ ρ := by
    have h := hSecond.of_monotone_intervalIntegral
      (add_pos hρ zero_lt_one) (Or.inl hH₁mono) hH₁pos hH₁int
    simpa [secondTailIntegral, H₁, add_sub_cancel_right] using h

  have hHpos : ∀ᶠ x : ℝ in atTop, 0 < H x := by
    by_contra hnot
    have hfrequent : ∃ᶠ x : ℝ in atTop, H x ≤ 0 := by
      simpa [not_lt] using (Filter.not_eventually.mp hnot)
    obtain ⟨R, hR⟩ := eventually_atTop.1 hH₁reg.eventually_pos
    obtain ⟨x, hxR, hxBad⟩ :=
      (hfrequent.and_eventually (eventually_ge_atTop (max R 1))).exists
    have hxPos : 0 < x := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (le_max_right R 1)) hxBad
    have hxZero : H x = 0 := le_antisymm hxR (hHnonneg x)
    have htailZero : ∀ y, x ≤ y → H y = 0 := by
      intro y hxy
      apply le_antisymm
      · calc
          H y ≤ H x := hanti hxy
          _ = 0 := hxZero
      · exact hHnonneg y
    have hH₁stable : ∀ y, x ≤ y → H₁ y = H₁ x := by
      intro y hxy
      have hxy0 : 0 ≤ x := le_of_lt hxPos
      have hy0 : 0 ≤ y := le_trans hxy0 hxy
      have hzeroOn : EqOn (fun t : ℝ => t * H t) (fun _ => 0) (uIcc x y) := by
        intro t ht
        rw [uIcc_of_le hxy] at ht
        simp [htailZero t ht.1]
      have hzeroInt : (∫ t in x..y, t * H t) = 0 := by
        rw [intervalIntegral.integral_congr hzeroOn]
        simp
      have hadd := intervalIntegral.integral_add_adjacent_intervals (hHint 0 x) (hHint x y)
      have hstable : H₁ y = H₁ x + ∫ t in x..y, t * H t := by
        dsimp [H₁, firstTailIntegral]
        rw [max_eq_left hy0, max_eq_left hxy0]
        exact hadd.symm
      rw [hzeroInt] at hstable
      linarith
    have hxR' : R ≤ x := le_trans (le_max_left R 1) hxBad
    have hFx : 0 < H₁ x := hR x hxR'
    have heq : (fun y : ℝ => H₁ (2*y) / H₁ y) =ᶠ[atTop] fun _ => 1 := by
      filter_upwards [eventually_ge_atTop x, eventually_ge_atTop R] with y hy hyR
      have hyx : x ≤ 2*y := by nlinarith [hxPos.le, hy]
      rw [hH₁stable (2*y) hyx, hH₁stable y hy]
      simp [ne_of_gt hFx]
    have hratio := hH₁reg.ratio_tendsto (c := 2) (by norm_num : (0:ℝ) < 2)
    have hlimEq : (1:ℝ) = 2 ^ ρ :=
      tendsto_nhds_unique tendsto_const_nhds (hratio.congr' heq)
    have hpow : 1 < (2:ℝ) ^ ρ := by
      exact Real.one_lt_rpow (by norm_num) hρ
    linarith

  have hGanti : Antitone G := by
    intro x y hxy
    exact hanti (Real.sqrt_le_sqrt hxy)
  have hGpos : ∀ᶠ y : ℝ in atTop, 0 < G y :=
    Real.tendsto_sqrt_atTop.eventually hHpos
  have hGint : ∀ a b : ℝ, IntervalIntegrable G volume a b :=
    fun a b => hGanti.intervalIntegrable
  let J : ℝ → ℝ := fun y => ∫ s in (0:ℝ)..y, G s
  have hchange (y : ℝ) (hy : 0 ≤ y) : J y = 2 * H₁ (Real.sqrt y) := by
    have hsqrt : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
    have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0:ℝ)) (b := Real.sqrt y)
      (f := fun t : ℝ => t ^ 2) (f' := fun t => 2*t)
      (g := fun s : ℝ => H (Real.sqrt s))
      (by fun_prop)
      (by
        intro t ht
        simpa using hasDerivAt_pow 2 t)
      (by
        intro t ht
        have ht0 : 0 < t := by
          simpa [min_eq_left hsqrt, max_eq_right hsqrt] using ht.1
        exact mul_nonneg (by norm_num) ht0.le)
    have hleft : (∫ t in (0:ℝ)..Real.sqrt y,
        (fun s : ℝ => H (Real.sqrt s)) (t ^ 2) * (2*t)) =
        2 * H₁ (Real.sqrt y) := by
      have heq : EqOn
          (fun t : ℝ => H (Real.sqrt (t ^ 2)) * (2*t))
          (fun t => 2 * (t * H t)) (uIcc 0 (Real.sqrt y)) := by
        intro t ht
        have ht0 : 0 ≤ t := by
          simpa [uIcc_of_le hsqrt] using ht.1
        change H (Real.sqrt (t ^ 2)) * (2*t) = 2 * (t * H t)
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht0]
        ring
      calc
        (∫ t in (0:ℝ)..Real.sqrt y,
            (fun s : ℝ => H (Real.sqrt s)) (t ^ 2) * (2*t))
            = ∫ t in (0:ℝ)..Real.sqrt y, 2 * (t * H t) :=
              intervalIntegral.integral_congr heq
        _ = 2 * H₁ (Real.sqrt y) := by
          rw [intervalIntegral.integral_const_mul]
          dsimp [H₁, firstTailIntegral]
          rw [max_eq_left hsqrt]
    calc
      J y = ∫ t in (0:ℝ)..Real.sqrt y,
          (fun s : ℝ => H (Real.sqrt s)) (t ^ 2) * (2*t) := by
            dsimp [J]
            have hsub' : (∫ t in (0:ℝ)..Real.sqrt y,
                (fun s : ℝ => H (Real.sqrt s)) (t ^ 2) * (2*t)) =
                ∫ u in (0:ℝ)..y, H (Real.sqrt u) := by
              simpa [hsq] using hsub
            exact hsub'.symm
      _ = 2 * H₁ (Real.sqrt y) := hleft
  have hJRV : IsRegularlyVaryingAtTop J (ρ / 2) := by
    have hcomp := hH₁reg.comp_rpow (by norm_num : (0:ℝ) < (1:ℝ)/2)
    have hcomp' : IsRegularlyVaryingAtTop
        (fun y : ℝ => H₁ (Real.sqrt y)) (ρ / 2) := by
      simpa [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_comm] using hcomp
    have hconst : IsRegularlyVaryingAtTop (fun _ : ℝ => (2:ℝ)) 0 := by
      change IsSlowlyVaryingAtTop (fun _ : ℝ => (2:ℝ))
      exact IsSlowlyVaryingAtTop.of_tendsto_pos (by norm_num) tendsto_const_nhds
    have hmul := hconst.mul hcomp'
    have hJ : J =ᶠ[atTop] fun y => 2 * H₁ (Real.sqrt y) := by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
      exact hchange y hy
    simpa using hmul.congr hJ.symm
  have hGreg : IsRegularlyVaryingAtTop G (ρ / 2 - 1) := by
    have h := hJRV.of_monotone_intervalIntegral
      (by linarith : 0 < ρ/2) (Or.inr hGanti) hGpos hGint
    simpa [J, sub_add_cancel] using h
  have hGsq := hGreg.comp_rpow (by norm_num : (0:ℝ) < 2)
  have hGsqEq : (fun x : ℝ => G (x ^ (2:ℝ))) =ᶠ[atTop] H := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    change H (Real.sqrt (x ^ (2:ℝ))) = H x
    rw [Real.rpow_two, Real.sqrt_sq_eq_abs, abs_of_pos hx]
  have hindex : 2 * (ρ / 2 - 1) = ρ - 2 := by ring
  simpa [hindex] using hGsq.congr hGsqEq

/-- For a bounded nonnegative antitone function and `0 < α < 2`, regular
variation of its tail is equivalent to regular variation of the associated
twice-integrated tail. -/
theorem IsRegularlyVaryingAtTop.secondTailIntegral_iff
    {H : ℝ → ℝ} {α : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hanti : Antitone H)
    (hHnonneg : ∀ x, 0 ≤ H x)
    (hHleOne : ∀ ⦃x : ℝ⦄, 0 ≤ x → H x ≤ 1)
    (hHint : ∀ a b : ℝ,
      IntervalIntegrable (fun t : ℝ => t * H t) volume a b) :
    IsRegularlyVaryingAtTop H (-α) ↔
      IsRegularlyVaryingAtTop (secondTailIntegral H) (3 - α) := by
  constructor
  · intro hreg
    exact hreg.isRegularlyVaryingAtTop_secondTailIntegral
      hα₀ hα₂ hanti hHnonneg hHleOne hHint
  · intro hsecond
    have hsecond' : IsRegularlyVaryingAtTop
        (secondTailIntegral H) ((2 - α) + 1) := by
      simpa only [show (2 - α) + 1 = 3 - α by ring] using hsecond
    have h := IsRegularlyVaryingAtTop.of_secondTailIntegral
      (ρ := 2 - α) (by linarith) hanti hHnonneg hHint hsecond'
    simpa only [show (2 - α) - 2 = -α by ring] using h

end Asymptotics

end

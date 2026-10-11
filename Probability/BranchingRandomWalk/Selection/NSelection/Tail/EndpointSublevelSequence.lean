/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Tail.RawRate

/-!
# Logarithmic-scale conversion for the selected-population endpoint sublevel

This file converts the finite-horizon decomposition in `RawRate` into a
polynomial bound under the logarithmic scales appearing in (4.16).
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown
open ProbabilityTheory.BranchingRandomWalk.Spine

private theorem tendsto_log_add_one_div_log_of_cubic_scale
    {u L : ℕ → ℝ} {t : ℝ}
    (hL : Tendsto L atTop atTop)
    (hu : ∀ n, 0 ≤ u n)
    (hscale : Tendsto (fun n => u n / L n ^ 3) atTop (𝓝 t))
    (ht : 0 < t) :
    Tendsto (fun n => Real.log (u n + 1) / L n) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0) :=
    hL.inv_tendsto_atTop
  have hinvCube : Tendsto (fun n => (L n)⁻¹ ^ 3) atTop (𝓝 0) := by
    simpa using hinv.pow 3
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have hscaled : Tendsto (fun n => (u n + 1) / L n ^ 3)
      atTop (𝓝 t) := by
    have hsum := hscale.add hinvCube
    have heq : (fun n => (u n + 1) / L n ^ 3) =ᶠ[atTop]
        fun n => u n / L n ^ 3 + (L n)⁻¹ ^ 3 := by
      filter_upwards [hLpos] with n hn
      field_simp
    simpa using hsum.congr' heq.symm
  have hlogScaled : Tendsto
      (fun n => Real.log ((u n + 1) / L n ^ 3)) atTop (𝓝 (Real.log t)) :=
    (Real.continuousAt_log (ne_of_gt ht)).tendsto.comp hscaled
  have hlogScaledDiv : Tendsto
      (fun n => Real.log ((u n + 1) / L n ^ 3) / L n)
      atTop (𝓝 0) := hlogScaled.div_atTop hL
  have hlogLDiv : Tendsto (fun n => Real.log (L n) / L n)
      atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1
      (by norm_num : (1 : ℝ) ≠ 0)).comp hL
    convert h using 1
    ext n
    simp [pow_one]
  have hsum := hlogScaledDiv.add (hlogLDiv.const_mul 3)
  have heq : (fun n => Real.log (u n + 1) / L n) =ᶠ[atTop]
      fun n => Real.log ((u n + 1) / L n ^ 3) / L n +
        3 * (Real.log (L n) / L n) := by
    filter_upwards [hLpos] with n hn
    have hu1 : 0 < u n + 1 := by linarith [hu n]
    rw [Real.log_div (ne_of_gt hu1) (pow_ne_zero 3 (ne_of_gt hn)),
      Real.log_pow]
    field_simp
    ring
  simpa using hsum.congr' heq.symm

private theorem tendsto_horizon_div_square_div_log
    {H B L : ℕ → ℝ} {t b : ℝ}
    (hL : Tendsto L atTop atTop)
    (hH : Tendsto (fun n => H n / L n ^ 3) atTop (𝓝 t))
    (hB : Tendsto (fun n => B n / L n) atTop (𝓝 b))
    (hb : 0 < b) :
    Tendsto (fun n => (H n / B n ^ 2) / L n)
      atTop (𝓝 (t / b ^ 2)) := by
  have hden : Tendsto (fun n => (B n / L n) ^ 2) atTop (𝓝 (b ^ 2)) :=
    hB.pow 2
  have hratio : Tendsto (fun n => (H n / L n ^ 3) / (B n / L n) ^ 2)
      atTop (𝓝 (t / b ^ 2)) :=
    hH.div hden (ne_of_gt (sq_pos_of_pos hb))
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have hBne : ∀ᶠ n : ℕ in atTop, B n ≠ 0 := by
    have hBpositive : ∀ᶠ n : ℕ in atTop, 0 < B n / L n := by
      filter_upwards [hB.eventually (Ioi_mem_nhds (by linarith : b / 2 < b))]
        with n hn
      linarith
    filter_upwards [hLpos, hBpositive] with n hLn hBn
    have hprod : 0 < (B n / L n) * L n := mul_pos hBn hLn
    have heq : (B n / L n) * L n = B n := by field_simp
    rw [heq] at hprod
    exact ne_of_gt hprod
  have heq : (fun n => (H n / B n ^ 2) / L n) =ᶠ[atTop]
      fun n => (H n / L n ^ 3) / (B n / L n) ^ 2 := by
    filter_upwards [hLpos, hBne] with n hLn hBn
    field_simp
  exact hratio.congr' heq.symm

/-- The raw finite-horizon endpoint decomposition has a polynomial bound when
the large-drop scale is `b log N`, the horizon is `t log^3 N`, the endpoint
threshold is `ζ log N`, and the selected population has size at most `N^a`.
The effective drawdown rate is `q`; the strict inequality is precisely the
remaining exponent margin in (4.16). -/
theorem eventually_probability_le_polynomial_of_raw_endpoint_bound
    {P : ℕ → ℝ≥0∞} {m N H : ℕ → ℕ} {B threshold : ℕ → ℝ}
    {a b t zeta q : ℝ}
    (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3)
      atTop (𝓝 t))
    (hB : Tendsto (fun n => B n / Real.log (N n : ℝ)) atTop (𝓝 b))
    (hthreshold : Tendsto
      (fun n => threshold n / Real.log (N n : ℝ)) atTop (𝓝 zeta))
    (ht : 0 < t) (hb : 1 < b)
    (hmargin : a + zeta < q * t / b ^ 2)
    (hm : ∀ᶠ n : ℕ in atTop, (m n : ℝ) ≤ (N n : ℝ) ^ a)
    (hraw : ∀ᶠ n : ℕ in atTop,
      P n ≤ (N n : ℝ≥0∞) *
          (((H n : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B n))) +
        (m n : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp (threshold n)) *
            ENNReal.ofReal (Real.exp
              (-q * ((H n : ℝ) / B n ^ 2))))) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ᶠ n : ℕ in atTop,
      P n ≤ ENNReal.ofReal (Real.exp (-epsilon * Real.log (N n : ℝ))) := by
  let L : ℕ → ℝ := fun n => Real.log (N n : ℝ)
  let U : ℕ → ℝ := fun n => (H n : ℝ)
  have hNcast : Tendsto (fun n => (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp hNcast
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have hUscale : Tendsto (fun n => U n / L n ^ 3) atTop (𝓝 t) := by
    simpa [L, U] using hH
  have hBscale : Tendsto (fun n => B n / L n) atTop (𝓝 b) := by
    simpa [L] using hB
  have hthresholdScale : Tendsto (fun n => threshold n / L n)
      atTop (𝓝 zeta) := by
    simpa [L] using hthreshold
  have hlogH : Tendsto (fun n => Real.log (U n + 1) / L n)
      atTop (𝓝 0) :=
    tendsto_log_add_one_div_log_of_cubic_scale hL
      (fun n => Nat.cast_nonneg (H n)) hUscale ht
  have hHB : Tendsto (fun n => (U n / B n ^ 2) / L n)
      atTop (𝓝 (t / b ^ 2)) :=
    tendsto_horizon_div_square_div_log hL hUscale hBscale (by linarith)
  have hrate1 : Tendsto
      (fun n => (L n + 2 * Real.log (U n + 1) - B n) / L n)
      atTop (𝓝 (1 - b)) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hsum := (hone.add (hlogH.const_mul 2)).sub hBscale
    have heq : (fun n => (L n + 2 * Real.log (U n + 1) - B n) / L n) =ᶠ[atTop]
        fun n => 1 + 2 * (Real.log (U n + 1) / L n) - B n / L n := by
      filter_upwards [hLpos] with n hn
      field_simp
    simpa using hsum.congr' heq.symm
  have hrate2 : Tendsto
      (fun n => (a * L n + threshold n - q * (U n / B n ^ 2)) / L n)
      atTop (𝓝 (a + zeta - q * (t / b ^ 2))) := by
    have ha : Tendsto (fun _ : ℕ => (a : ℝ)) atTop (𝓝 a) := tendsto_const_nhds
    have hsum := (ha.add hthresholdScale).sub (hHB.const_mul q)
    have heq : (fun n => (a * L n + threshold n - q * (U n / B n ^ 2)) / L n)
        =ᶠ[atTop] fun n => a + threshold n / L n -
          q * ((U n / B n ^ 2) / L n) := by
      filter_upwards [hLpos] with n hn
      field_simp
    simpa using hsum.congr' heq.symm
  let epsilon : ℝ := min (b - 1) (q * t / b ^ 2 - (a + zeta)) / 4
  have hgap1 : 0 < b - 1 := by linarith
  have hgap2 : 0 < q * t / b ^ 2 - (a + zeta) := by linarith
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hrate1gap : 1 - b < -2 * epsilon := by
    dsimp [epsilon]
    have hmin : min (b - 1) (q * t / b ^ 2 - (a + zeta)) ≤ b - 1 :=
      min_le_left _ _
    linarith
  have hrate2gap : a + zeta - q * (t / b ^ 2) < -2 * epsilon := by
    dsimp [epsilon]
    have hmin : min (b - 1) (q * t / b ^ 2 - (a + zeta)) ≤
        q * t / b ^ 2 - (a + zeta) := min_le_right _ _
    have hbpos : 0 < b := by linarith
    have hratio : q * (t / b ^ 2) = q * t / b ^ 2 := by ring
    rw [hratio]
    linarith
  have hrate1event : ∀ᶠ n : ℕ in atTop,
      (L n + 2 * Real.log (U n + 1) - B n) / L n < -2 * epsilon :=
    hrate1.eventually (Iio_mem_nhds hrate1gap)
  have hrate2event : ∀ᶠ n : ℕ in atTop,
      (a * L n + threshold n - q * (U n / B n ^ 2)) / L n < -2 * epsilon :=
    hrate2.eventually (Iio_mem_nhds hrate2gap)
  have hlogLarge : ∀ᶠ n : ℕ in atTop, Real.log 2 < epsilon * L n := by
    have hmul : Tendsto (fun n => epsilon * L n) atTop atTop :=
      hL.const_mul_atTop hepsilon
    exact hmul.eventually_gt_atTop (Real.log 2)
  have hpowN : ∀ᶠ n : ℕ in atTop,
      (N n : ℝ) = Real.exp (L n) := by
    filter_upwards [hLpos] with n hn
    have hnNat : 0 < N n := by
      by_contra h
      have hz : N n = 0 := Nat.eq_zero_of_not_pos h
      simp [L, hz] at hn
    have hnReal : 0 < (N n : ℝ) := by exact_mod_cast hnNat
    simp [L, Real.exp_log hnReal]
  refine ⟨epsilon, hepsilon, ?_⟩
  filter_upwards [hraw, hm, hrate1event, hrate2event, hlogLarge, hLpos,
      hpowN] with n hrawn hmn hrate1n hrate2n hlogLarg nLpos hpowNn
  have hNpos : 0 < (N n : ℝ) := by
    have hnNat : 0 < N n := by
      by_contra h
      have hz : N n = 0 := Nat.eq_zero_of_not_pos h
      simp [L, hz] at nLpos
    exact_mod_cast hnNat
  have hUplus : 0 < U n + 1 := by dsimp [U]; positivity
  have hrate1real : L n + 2 * Real.log (U n + 1) - B n <
      -2 * epsilon * L n := (div_lt_iff₀ nLpos).mp hrate1n
  have hrate2real : a * L n + threshold n - q * (U n / B n ^ 2) <
      -2 * epsilon * L n := (div_lt_iff₀ nLpos).mp hrate2n
  have hexp1 : Real.exp (L n + 2 * Real.log (U n + 1) - B n) ≤
      Real.exp (-2 * epsilon * L n) := Real.exp_le_exp.mpr hrate1real.le
  have hexp2 : Real.exp (a * L n + threshold n - q * (U n / B n ^ 2)) ≤
      Real.exp (-2 * epsilon * L n) := Real.exp_le_exp.mpr hrate2real.le
  have hNatSquareCast : ((H n : ℝ≥0∞) + 1) ^ 2 =
      ENNReal.ofReal (((H n : ℝ) + 1) ^ 2) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (Nat.cast_nonneg (H n)) (by norm_num : (0 : ℝ) ≤ 1),
      ENNReal.ofReal_pow (by positivity : 0 ≤ (H n : ℝ) + 1)]
  have hfirstEq : (N n : ℝ≥0∞) *
      (((H n : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B n))) =
      ENNReal.ofReal (Real.exp (L n + 2 * Real.log (U n + 1) - B n)) := by
    rw [hNatSquareCast, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ ((H n : ℝ) + 1) ^ 2),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (N n : ℝ))]
    rw [hpowNn]
    have hpow : (U n + 1) ^ 2 = Real.exp (2 * Real.log (U n + 1)) := by
      calc
        (U n + 1) ^ 2 = (Real.exp (Real.log (U n + 1))) ^ 2 := by
          rw [Real.exp_log hUplus]
        _ = Real.exp (2 * Real.log (U n + 1)) := by
          rw [← Real.exp_nat_mul]
          congr 1
    rw [hpow]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hmENN : (m n : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (a * L n)) := by
    calc
      (m n : ℝ≥0∞) = ENNReal.ofReal (m n : ℝ) :=
        (ENNReal.ofReal_natCast (m n)).symm
      _ ≤ ENNReal.ofReal ((N n : ℝ) ^ a) :=
        ENNReal.ofReal_le_ofReal hmn
      _ = ENNReal.ofReal (Real.exp (a * L n)) := by
        rw [Real.rpow_def_of_pos hNpos]
        dsimp [L]
        congr 1
        ring
  have hsecondUpper : (m n : ℝ≥0∞) *
      (ENNReal.ofReal (Real.exp (threshold n)) *
        ENNReal.ofReal (Real.exp (-q * (U n / B n ^ 2)))) ≤
      ENNReal.ofReal (Real.exp (a * L n + threshold n - q * (U n / B n ^ 2))) := by
    calc
      _ ≤ ENNReal.ofReal (Real.exp (a * L n)) *
          (ENNReal.ofReal (Real.exp (threshold n)) *
            ENNReal.ofReal (Real.exp (-q * (U n / B n ^ 2)))) :=
        mul_le_mul_of_nonneg_right hmENN (by positivity)
      _ = ENNReal.ofReal (Real.exp (a * L n + threshold n -
          q * (U n / B n ^ 2))) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (threshold n)),
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (a * L n))]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hsumUpper :
      (N n : ℝ≥0∞) *
          (((H n : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B n))) +
        (m n : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp (threshold n)) *
            ENNReal.ofReal (Real.exp (-q * (U n / B n ^ 2)))) ≤
      ENNReal.ofReal (2 * Real.exp (-2 * epsilon * L n)) := by
    rw [hfirstEq]
    calc
      _ ≤ ENNReal.ofReal (Real.exp (-2 * epsilon * L n)) +
          ENNReal.ofReal (Real.exp (-2 * epsilon * L n)) := by
        exact add_le_add
          (ENNReal.ofReal_le_ofReal hexp1)
          (le_trans hsecondUpper (ENNReal.ofReal_le_ofReal hexp2))
      _ = ENNReal.ofReal (2 * Real.exp (-2 * epsilon * L n)) := by
        rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
        congr 1
        ring
  have hlarge : 2 ≤ Real.exp (epsilon * L n) := by
    have hexp : Real.exp (Real.log 2) < Real.exp (epsilon * L n) :=
      Real.exp_lt_exp.mpr hlogLarg
    have htwo : Real.exp (Real.log 2) = (2 : ℝ) := by
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [htwo] at hexp
    exact hexp.le
  have hsumToFinal : 2 * Real.exp (-2 * epsilon * L n) ≤
      Real.exp (-epsilon * L n) := by
    calc
      2 * Real.exp (-2 * epsilon * L n) ≤
          Real.exp (epsilon * L n) * Real.exp (-2 * epsilon * L n) :=
        mul_le_mul_of_nonneg_right hlarge (Real.exp_nonneg _)
      _ = Real.exp (-epsilon * L n) := by
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    P n ≤ (N n : ℝ≥0∞) *
          (((H n : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B n))) +
        (m n : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp (threshold n)) *
            ENNReal.ofReal (Real.exp (-q * (U n / B n ^ 2)))) := hrawn
    _ ≤ ENNReal.ofReal (2 * Real.exp (-2 * epsilon * L n)) := hsumUpper
    _ ≤ ENNReal.ofReal (Real.exp (-epsilon * L n)) :=
      ENNReal.ofReal_le_ofReal hsumToFinal
    _ = ENNReal.ofReal (Real.exp (-epsilon * Real.log (N n : ℝ))) := by
      rfl


/-- A selected-population endpoint bound follows from the raw finite-horizon
bound in `RawRate` and the logarithmic scale assumptions.  This is the short
composition interface: the raw bound is supplied by
`eventually_finiteRootStepFieldLaw_firstNSelectedEndpointBelow_le_of_rangeRate`.
-/
theorem eventually_finiteRootStepFieldLaw_firstNSelectedEndpointBelow_le_polynomial_of_rawRate
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {m N H : ℕ → ℕ} (horder : ∀ n,
      LinearOrder (RootIndexed.TreeNode (Fin (m n)) ℕ))
    {B threshold : ℕ → ℝ} {a b t zeta q : ℝ}
    (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3)
      atTop (𝓝 t))
    (hB : Tendsto (fun n => B n / Real.log (N n : ℝ)) atTop (𝓝 b))
    (hthreshold : Tendsto
      (fun n => threshold n / Real.log (N n : ℝ)) atTop (𝓝 zeta))
    (ht : 0 < t) (hb : 1 < b)
    (hm : ∀ᶠ n : ℕ in atTop, (m n : ℝ) ≤ (N n : ℝ) ^ a)
    (hmargin : a + zeta < q * t / b ^ 2)
    (hraw : ∀ᶠ n : ℕ in atTop,
      (finiteRootStepFieldLaw μ (m n))
        (@firstNSelectedEndpointBelow (m n) (N n) (H n) (horder n)
          (threshold n)) ≤
      (N n : ℝ≥0∞) *
          (((H n : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B n))) +
        (m n : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp (threshold n)) *
            ENNReal.ofReal (Real.exp (-q * ((H n : ℝ) / B n ^ 2))))) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ᶠ n : ℕ in atTop,
      (finiteRootStepFieldLaw μ (m n))
        (@firstNSelectedEndpointBelow (m n) (N n) (H n) (horder n)
          (threshold n)) ≤
        ENNReal.ofReal (Real.exp (-epsilon * Real.log (N n : ℝ))) := by
  let P : ℕ → ℝ≥0∞ := fun n =>
    (finiteRootStepFieldLaw μ (m n))
      (@firstNSelectedEndpointBelow (m n) (N n) (H n) (horder n)
        (threshold n))
  have hrawP : ∀ᶠ n : ℕ in atTop,
      P n ≤ (N n : ℝ≥0∞) *
          (((H n : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B n))) +
        (m n : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp (threshold n)) *
            ENNReal.ofReal (Real.exp (-q * ((H n : ℝ) / B n ^ 2)))) := by
    simpa [P] using hraw
  have hpost := eventually_probability_le_polynomial_of_raw_endpoint_bound
    (P := P) (m := m) (N := N) (H := H) (B := B)
    (threshold := threshold) (a := a) (b := b) (t := t) (zeta := zeta)
    (q := q) hN hH hB hthreshold ht hb hmargin hm hrawP
  simpa [P] using hpost

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

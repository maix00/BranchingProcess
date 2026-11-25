/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Analysis.Asymptotics.Sequence.LogarithmicScale
import Analysis.Asymptotics.Scale.Power.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Exponent assembly for actual family-cutoff corridor success

## Internal proof declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.cutoffCorridor_cubicScaleFacts`:
  if `Lₙ→∞` and `Hₙ/Lₙ³→t>0`, then `Hₙ>0` eventually,
  `Lₙ²/Hₙ→0`, `Lₙ^(1/2)/Lₙ→0` and `log(Hₙ+1)/Lₙ→0`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.eventually_cutoffCorridor_expBudget_le_ratio`:
  on the cubic scale, every
  `β>α+4ρ+a+1/2+2(dLower-dUpper)t` gives `exp(-βLₙ)≤Mₙ²/Sₙ` eventually.

These are the specific exponent calculations following the cutoff first and
MRCA second moments in B. Mallein, *N-branching random walk with α-stable
spine*, proof of Lemma 3.4, arXiv:1503.03762v2. Generic power/log limits
and ENNReal quotient comparisons use the existing analysis and Mathlib APIs.
No new public budget definition is introduced.
-/

namespace ProbabilityTheory.BranchingRandomWalk.Spine
open Filter
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency false

lemma cutoffCorridor_cubicScaleFacts {L : ℕ → ℝ} {H : ℕ → ℕ} {t : ℝ}
    (hL : Tendsto L atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / L n ^ 3) atTop (𝓝 t)) (ht : 0 < t) :
    (∀ᶠ n in atTop, 0 < H n) ∧
      Tendsto (fun n => L n ^ 2 / (H n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n => L n ^ (1 / 2 : ℝ) / L n) atTop (𝓝 0) ∧
      Tendsto (fun n => Real.log ((H n : ℝ) + 1) / L n) atTop (𝓝 0) := by
  have hpos := hL.eventually_gt_atTop 0
  have hHpos : ∀ᶠ n in atTop, 0 < H n := by
    filter_upwards [hpos, hH.eventually (Ioi_mem_nhds ht)] with n hn hratio
    have hh := (lt_div_iff₀ (pow_pos hn 3)).1 hratio
    simp only [zero_mul] at hh
    exact_mod_cast hh
  have hsmall : Tendsto (fun n => L n ^ 2 / (H n : ℝ)) atTop (𝓝 0) := by
    have hh : Tendsto (fun n => (H n : ℝ) / L n ^ (3 : ℝ)) atTop (𝓝 t) := by
      simpa only [Real.rpow_ofNat] using hH
    have h := Asymptotics.tendsto_rpow_div_of_ratio_limit hL hh ht.ne' (by norm_num : (2 : ℝ) < 3)
    simpa only [Real.rpow_two] using h
  have hsqrt : Tendsto (fun n => L n ^ (1 / 2 : ℝ) / L n) atTop (𝓝 0) := by
    have hh : Tendsto (fun n => L n / L n ^ (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hpos] with n hn
      simp [hn.ne']
    exact Asymptotics.tendsto_rpow_div_of_ratio_limit hL hh one_ne_zero (by norm_num)
  have hpoly : ∀ᶠ n in atTop, (H n : ℝ) ≤ (t + 1) * L n ^ (3 : ℝ) := by
    filter_upwards [hpos, hH.eventually (Iio_mem_nhds (lt_add_one t))] with n hn hratio
    rw [show L n ^ (3 : ℝ) = L n ^ (3 : ℕ) from Real.rpow_natCast (L n) 3]
    exact ((div_lt_iff₀ (pow_pos hn 3)).1 hratio).le
  have hlog := Asymptotics.tendsto_log_add_one_div_scale_of_power_bound hL
    (Eventually.of_forall (fun n => Nat.cast_nonneg (H n))) (by linarith : 0 ≤ t + 1)
    (by norm_num : (0 : ℝ) < 3) hpoly
  exact ⟨hHpos, hsmall, hsqrt, hlog⟩

private lemma cutoffCorridor_expBudget_le_ratio {L α a b ρ c dUpper dLower : ℝ} (H : ℕ)
    (hL : 0 < L) (hα : 0 ≤ α) (hb : -(1 / 2 : ℝ) < b) (hρ : 0 < ρ)
    (hd : 0 ≤ dUpper) (hc : dUpper ≤ c) :
    let lower := -(a + 1 / 2) * L
    let U := (b + ρ - a) * L + c * (H : ℝ) / L ^ 2
    let M := ENNReal.ofReal (Real.exp ((b - ρ - a) * L + (c - dLower) * (H : ℝ) / L ^ 2))
    let S := ENNReal.ofReal (Real.exp (α * L)) * ENNReal.ofReal (Real.exp
      (3 * L ^ (1 / 2 : ℝ) + 2 * U - 2 * dUpper * ((H : ℝ) - 1) / L ^ 2)) *
        (∑ m : Fin H, ENNReal.ofReal (Real.exp
          (dUpper * (m.val : ℝ) / L ^ 2 - (lower + c / L ^ 2 * (m.val : ℝ))))) +
        ENNReal.ofReal (Real.exp (U + L ^ (1 / 2 : ℝ) - dUpper * (H : ℝ) / L ^ 2))
    ENNReal.ofReal (Real.exp (-((α + 4 * ρ + a + 1 / 2) * L +
      2 * (dLower - dUpper) * (H : ℝ) / L ^ 2 + 3 * L ^ (1 / 2 : ℝ) +
      2 * dUpper / L ^ 2 + Real.log ((H : ℝ) + 1)))) ≤ M ^ 2 / S := by
  intro lower U M S
  let B := α * L + 3 * L ^ (1 / 2 : ℝ) + 2 * U -
    2 * dUpper * ((H : ℝ) - 1) / L ^ 2 - lower
  have hsum : (∑ m : Fin H, ENNReal.ofReal (Real.exp
      (dUpper * (m.val : ℝ) / L ^ 2 - (lower + c / L ^ 2 * (m.val : ℝ))))) ≤
      (H : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-lower)) := by
    calc
      _ ≤ ∑ _m : Fin H, ENNReal.ofReal (Real.exp (-lower)) := by
        apply Finset.sum_le_sum
        intro m _
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg m.val)
        have hh := div_le_div_of_nonneg_right h (sq_nonneg L)
        rw [div_mul_eq_mul_div]
        linarith only [hh]
      _ = _ := by simp
  have hdiag : U + L ^ (1 / 2 : ℝ) - dUpper * (H : ℝ) / L ^ 2 ≤ B := by
    have h1 := mul_nonneg hα hL.le
    have h2 := Real.rpow_nonneg hL.le (1 / 2 : ℝ)
    have h3 := mul_nonneg (show 0 ≤ b + ρ + 1 / 2 by linarith) hL.le
    have h4 := div_nonneg (mul_nonneg (sub_nonneg.mpr hc) (Nat.cast_nonneg H)) (sq_nonneg L)
    have h5 := div_nonneg hd (sq_nonneg L)
    apply sub_nonneg.mp
    calc
      0 ≤ α * L + 2 * L ^ (1 / 2 : ℝ) + (b + ρ + 1 / 2) * L +
          (c - dUpper) * (H : ℝ) / L ^ 2 + 2 * (dUpper / L ^ 2) := by
        linarith only [h1, h2, h3, h4, h5]
      _ = _ := by dsimp [B, U, lower]; ring
  have hS : S ≤ ((H : ℝ≥0∞) + 1) * ENNReal.ofReal (Real.exp B) := by
    have hoff := mul_le_mul' (le_refl (ENNReal.ofReal (Real.exp (α * L)) *
      ENNReal.ofReal (Real.exp (3 * L ^ (1 / 2 : ℝ) + 2 * U -
        2 * dUpper * ((H : ℝ) - 1) / L ^ 2)))) hsum
    have heq : ENNReal.ofReal (Real.exp (α * L)) *
        ENNReal.ofReal (Real.exp (3 * L ^ (1 / 2 : ℝ) + 2 * U -
          2 * dUpper * ((H : ℝ) - 1) / L ^ 2)) *
        ((H : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-lower))) =
        (H : ℝ≥0∞) * ENNReal.ofReal (Real.exp B) := by
      calc
        _ = (H : ℝ≥0∞) * ((ENNReal.ofReal (Real.exp (α * L)) *
            ENNReal.ofReal (Real.exp (3 * L ^ (1 / 2 : ℝ) + 2 * U -
              2 * dUpper * ((H : ℝ) - 1) / L ^ 2))) * ENNReal.ofReal (Real.exp (-lower))) := by ac_rfl
        _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add,
            ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
          rw [show α * L + (3 * L ^ (1 / 2 : ℝ) + 2 * U -
            2 * dUpper * ((H : ℝ) - 1) / L ^ 2) + -lower = B by dsimp [B]; ring]
    calc
      S ≤ (H : ℝ≥0∞) * ENNReal.ofReal (Real.exp B) + ENNReal.ofReal
          (Real.exp (U + L ^ (1 / 2 : ℝ) - dUpper * (H : ℝ) / L ^ 2)) :=
        add_le_add (hoff.trans_eq heq) le_rfl
      _ ≤ (H : ℝ≥0∞) * ENNReal.ofReal (Real.exp B) + ENNReal.ofReal (Real.exp B) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hdiag))
      _ = _ := by rw [add_mul, one_mul]
  let G := (α + 4 * ρ + a + 1 / 2) * L +
    2 * (dLower - dUpper) * (H : ℝ) / L ^ 2 + 3 * L ^ (1 / 2 : ℝ) +
    2 * dUpper / L ^ 2 + Real.log ((H : ℝ) + 1)
  have hidentity : ENNReal.ofReal (Real.exp (-G)) *
      (((H : ℝ≥0∞) + 1) * ENNReal.ofReal (Real.exp B)) = M ^ 2 := by
    have hcast : (H : ℝ≥0∞) + 1 = ENNReal.ofReal ((H : ℝ) + 1) := by
      rw [ENNReal.ofReal_add (Nat.cast_nonneg H) (by norm_num), ENNReal.ofReal_natCast,
        ENNReal.ofReal_one]
    rw [hcast, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (H : ℝ) + 1),
      ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    rw [show (H : ℝ) + 1 = Real.exp (Real.log ((H : ℝ) + 1)) from
      (Real.exp_log (by positivity)).symm, ← Real.exp_add, ← Real.exp_add]
    dsimp [M]
    rw [← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul]
    congr 2
    dsimp [G, B, U, lower]
    ring
  have hM : M ^ 2 ≠ 0 := by dsimp [M]; positivity
  apply (ENNReal.le_div_iff_mul_le (Or.inr hM) (Or.inr (by dsimp [M]; finiteness))).2
  exact (mul_le_mul' le_rfl hS).trans_eq hidentity

lemma eventually_cutoffCorridor_expBudget_le_ratio
    {L : ℕ → ℝ} {H : ℕ → ℕ} {t α a b ρ c dUpper dLower β : ℝ}
    (hL : Tendsto L atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / L n ^ 3) atTop (𝓝 t)) (ht : 0 < t)
    (hα : 0 ≤ α) (hb : -(1 / 2 : ℝ) < b) (hρ : 0 < ρ)
    (hd : 0 ≤ dUpper) (hc : dUpper ≤ c)
    (hβ : α + 4 * ρ + a + 1 / 2 + 2 * (dLower - dUpper) * t < β) :
    ∀ᶠ n in atTop,
      let lower := -(a + 1 / 2) * L n
      let U := (b + ρ - a) * L n + c * (H n : ℝ) / L n ^ 2
      let M := ENNReal.ofReal (Real.exp
        ((b - ρ - a) * L n + (c - dLower) * (H n : ℝ) / L n ^ 2))
      let S := ENNReal.ofReal (Real.exp (α * L n)) * ENNReal.ofReal (Real.exp
        (3 * L n ^ (1 / 2 : ℝ) + 2 * U - 2 * dUpper * ((H n : ℝ) - 1) / L n ^ 2)) *
          (∑ m : Fin (H n), ENNReal.ofReal (Real.exp
            (dUpper * (m.val : ℝ) / L n ^ 2 - (lower + c / L n ^ 2 * (m.val : ℝ))))) +
          ENNReal.ofReal (Real.exp (U + L n ^ (1 / 2 : ℝ) - dUpper * (H n : ℝ) / L n ^ 2))
      ENNReal.ofReal (Real.exp (-β * L n)) ≤ M ^ 2 / S := by
  obtain ⟨_, _, hsqrt, hlog⟩ := cutoffCorridor_cubicScaleFacts hL hH ht
  have hinv : Tendsto (fun n => 1 / L n) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hL
  let A := α + 4 * ρ + a + 1 / 2
  let G n := A * L n + 2 * (dLower - dUpper) * (H n : ℝ) / L n ^ 2 +
    3 * L n ^ (1 / 2 : ℝ) + 2 * dUpper / L n ^ 2 + Real.log ((H n : ℝ) + 1)
  have hnorm : Tendsto (fun n => G n / L n) atTop
      (𝓝 (A + 2 * (dLower - dUpper) * t)) := by
    have hh := ((((tendsto_const_nhds (x := A)).add (hH.const_mul (2 * (dLower - dUpper)))).add
      (hsqrt.const_mul 3)).add ((hinv.pow 3).const_mul (2 * dUpper))).add hlog
    simp only [mul_zero, add_zero, zero_pow (by omega : 3 ≠ 0)] at hh
    apply hh.congr'
    filter_upwards [hL.eventually_gt_atTop 0] with n hn
    dsimp [G]
    field_simp
  filter_upwards [hL.eventually_gt_atTop 0, hnorm.eventually (Iio_mem_nhds hβ)] with n hn hcost
  dsimp only
  refine (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)).trans
    (cutoffCorridor_expBudget_le_ratio (H n) hn hα hb hρ hd hc)
  change -β * L n ≤ -G n
  have hh := (div_lt_iff₀ hn).1 hcost
  linarith only [hh]

end ProbabilityTheory.BranchingRandomWalk.Spine

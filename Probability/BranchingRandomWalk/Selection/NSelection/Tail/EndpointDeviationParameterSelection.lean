/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Tail.EndpointDeviationParameters
public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.GaussianM3
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Parameter selection for the selected-endpoint sublevel exponent

This file turns the strict diffusive target inequality in (4.16) into the
range-rate and spatial-bin parameters used by `PolynomialEndpointSublevel`.  It is a
deterministic parameter lemma; no rate assumption is added to a probabilistic
theorem.
-/

@[expose] public section

open Filter
open scoped Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

private theorem tendsto_natSuccCast_atTop :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
  simpa using tendsto_atTop_add_const_right atTop (1 : ℝ)
    tendsto_natCast_atTop_atTop

private theorem tendsto_rangeCoverEnergy_atTop :
    Tendsto (fun n : ℕ =>
      (rangeCoverUnion (n + 1) (by omega : 0 < n + 1)).realEnergy)
      atTop (𝓝 (1 / 4 : ℝ)) := by
  have hindex : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natSuccCast_atTop
  have hinv : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹))
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hindex
  have hsum : Tendsto (fun n : ℕ =>
      (1 : ℝ) + (2 : ℝ) * (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 1) := by
    have htwo : Tendsto (fun n : ℕ =>
        (2 : ℝ) * (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hinv)
    simpa using (tendsto_const_nhds.add htwo)
  have hbase : Tendsto (fun n : ℕ =>
      (2 : ℝ) * (1 + 2 * (((n + 1 : ℕ) : ℝ)⁻¹))) atTop (𝓝 2) := by
    have h := hsum.const_mul (2 : ℝ)
    simpa using h
  have hpow : Tendsto (fun n : ℕ =>
      (2 * (1 + 2 * (((n + 1 : ℕ) : ℝ)⁻¹))) ^ (-2 : ℝ))
      atTop (𝓝 ((2 : ℝ) ^ (-2 : ℝ))) := by
    have hcont : ContinuousAt (fun x : ℝ => x ^ (-2 : ℝ)) 2 := by
      exact Real.continuousAt_rpow_const 2 (-2) (Or.inl (by norm_num))
    exact hcont.tendsto.comp hbase
  have hlimit : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  have hpow' : Tendsto (fun n : ℕ =>
      (2 * (1 + 2 / ((n + 1 : ℕ) : ℝ))) ^ (-2 : ℝ))
      atTop (𝓝 (1 / 4 : ℝ)) := by
    have heq : (fun n : ℕ =>
        (2 * (1 + 2 / ((n + 1 : ℕ) : ℝ))) ^ (-2 : ℝ)) =
      fun n => (2 * (1 + 2 * (((n + 1 : ℕ) : ℝ)⁻¹))) ^ (-2 : ℝ) := by
      funext n
      congr 2
    rw [heq]
    simpa [hlimit] using hpow
  have heq : (fun n : ℕ =>
      (rangeCoverUnion (n + 1) (by omega : 0 < n + 1)).realEnergy) =
    fun n => (2 * (1 + 2 / ((n + 1 : ℕ) : ℝ))) ^ (-2 : ℝ) := by
    funext n
    rw [rangeCoverUnion_realEnergy]
  rw [heq]
  exact hpow'

private theorem exists_small_positive_notInteger_ratio
    (r bound : ℝ) (hbound : 0 < bound) :
    ∃ eta : ℝ, 0 < eta ∧ eta < bound ∧
      (r / eta < 1 ∨ ¬ ∃ j : ℕ, r / eta = (j : ℝ)) := by
  by_cases hr : r ≤ 0
  · refine ⟨bound / 2, by positivity, by linarith, ?_⟩
    left
    exact (div_nonpos_of_nonpos_of_nonneg hr (by positivity)).trans_lt
      (by norm_num)
  · have hrpos : 0 < r := lt_of_not_ge hr
    have htop : Tendsto (fun n : ℕ =>
        (r / ((n : ℝ) + 1 / 2))) atTop (𝓝 0) := by
      have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1 / 2) atTop atTop := by
        simpa using tendsto_atTop_add_const_right atTop (1 / 2 : ℝ)
          tendsto_natCast_atTop_atTop
      have hinv : Tendsto (fun n : ℕ =>
          ((n : ℝ) + 1 / 2)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hden
      simpa [div_eq_mul_inv] using hinv.const_mul r
    obtain ⟨n, hn⟩ := htop.eventually (Iio_mem_nhds hbound) |>.exists
    refine ⟨r / ((n : ℝ) + 1 / 2), div_pos hrpos (by positivity), hn, ?_⟩
    right
    have hratio : r / (r / ((n : ℝ) + 1 / 2)) = (n : ℝ) + 1 / 2 := by
      field_simp
    rw [hratio]
    intro h
    rcases h with ⟨j, hj⟩
    have hnatReal : (2 * n + 1 : ℕ) = 2 * j := by
      have hcast : 2 * (n : ℝ) + 1 = 2 * (j : ℝ) := by linarith
      exact_mod_cast hcast
    omega

/-- Choose the exponent and block parameters required by the raw endpoint sublevel
estimate, assuming only the strict target inequality from (4.16).  In
particular, the spatial-bin nonresonance condition is chosen internally. -/
theorem exists_endpoint_sublevel_parameters_of_diffusive_gap
    {a t zeta sigma : ℝ} (ht : 0 < t)
    (hsigma : 0 < sigma)
    (hbelow : zeta < -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t) :
    ∃ b factor eta rangeRate targetRate : ℝ, ∃ k : ℕ, ∃ hk : 0 < k,
      1 < b ∧ 1 < factor ∧ 0 < eta ∧
      0 < rangeRate ∧
      rangeRate < (Real.pi ^ 2 / 2) * (rangeCoverUnion k hk).realEnergy ∧
      0 < targetRate ∧
      targetRate < rangeRate / (factor * (1 + eta) / 2) ^ 2 ∧
      ((zeta / b + 1) / eta < 1 ∨
        ¬ ∃ j : ℕ, (zeta / b + 1) / eta = (j : ℝ)) ∧
      a + zeta < (targetRate * sigma ^ 2) * t / b ^ 2 := by
  have hC : 0 < (Real.pi ^ 2 / 2) * sigma ^ 2 := by positivity
  have hpi : 0 < Real.pi ^ 2 / 2 := by positivity
  have hbelow' : zeta < -a + ((Real.pi ^ 2 / 2) * sigma ^ 2) * t := by
    exact hbelow
  obtain ⟨b, d, c, epsilon, hb, hd, hdC, hc, hcHalf, hcEndpoint,
      hepsilon, hepsilonB, hepsilonMargin⟩ :=
    exists_endpoint_deviation_parameters ht hC hbelow'
  have hsigmaSq : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
  let q₀ : ℝ := d / sigma ^ 2
  have hq₀ : 0 < q₀ := by dsimp [q₀]; exact div_pos hd hsigmaSq
  have hq₀Upper : q₀ < Real.pi ^ 2 / 2 := by
    dsimp [q₀]
    exact (div_lt_iff₀ hsigmaSq).2 (by simpa [mul_comm] using hdC)
  have hq₁ : q₀ < (q₀ + Real.pi ^ 2 / 2) / 2 := by linarith
  have hq₁Upper : (q₀ + Real.pi ^ 2 / 2) / 2 < Real.pi ^ 2 / 2 := by
    linarith
  let q₁ : ℝ := (q₀ + Real.pi ^ 2 / 2) / 2
  have hq₁pos : 0 < q₁ := by dsimp [q₁]; positivity
  have hratio : 1 < (Real.pi ^ 2 / 2) / q₁ :=
    (lt_div_iff₀ hq₁pos).2 (by simpa [mul_comm] using hq₁Upper)
  have hsqrtRatio : 1 < Real.sqrt ((Real.pi ^ 2 / 2) / q₁) := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hratio
    simpa using h
  let factor : ℝ := (1 + Real.sqrt ((Real.pi ^ 2 / 2) / q₁)) / 2
  have hfactor : 1 < factor := by dsimp [factor]; linarith
  have hfactorPos : 0 < factor := lt_trans zero_lt_one hfactor
  have hfactorSqrt : factor < Real.sqrt ((Real.pi ^ 2 / 2) / q₁) := by
    dsimp [factor]
    linarith
  have hfactorSq : q₁ * factor ^ 2 < Real.pi ^ 2 / 2 := by
    have hsqrtPos : 0 < Real.sqrt ((Real.pi ^ 2 / 2) / q₁) :=
      Real.sqrt_pos.2 (div_pos (by positivity) hq₁pos)
    have hprod :
        0 < (Real.sqrt ((Real.pi ^ 2 / 2) / q₁) - factor) *
          (Real.sqrt ((Real.pi ^ 2 / 2) / q₁) + factor) :=
      mul_pos (sub_pos.mpr hfactorSqrt) (add_pos hsqrtPos hfactorPos)
    have hsquare :
        (Real.sqrt ((Real.pi ^ 2 / 2) / q₁)) ^ 2 =
          (Real.pi ^ 2 / 2) / q₁ :=
      Real.sq_sqrt (div_nonneg (by positivity) hq₁pos.le)
    have hq : q₁ * factor ^ 2 < q₁ *
        ((Real.pi ^ 2 / 2) / q₁) := by nlinarith
    have heq : q₁ * ((Real.pi ^ 2 / 2) / q₁) = Real.pi ^ 2 / 2 := by
      field_simp [ne_of_gt hq₁pos]
    simpa [heq] using hq
  let etaLimit : ℝ := Real.sqrt ((Real.pi ^ 2 / 2) / (q₁ * factor ^ 2)) - 1
  have hetaLimit : 0 < etaLimit := by
    dsimp [etaLimit]
    have hratio' : 1 < (Real.pi ^ 2 / 2) / (q₁ * factor ^ 2) :=
      (lt_div_iff₀ (mul_pos hq₁pos (sq_pos_of_pos hfactorPos))).2
        (by simpa [one_mul] using hfactorSq)
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hratio'
    simpa using sub_pos.mpr h
  obtain ⟨eta, heta, hetaLimit', hbin⟩ :=
    exists_small_positive_notInteger_ratio (zeta / b + 1) etaLimit hetaLimit
  let beta : ℝ := factor * (1 + eta) / 2
  have hbetaPos : 0 < beta := by dsimp [beta]; positivity
  have hqbeta : q₁ * beta ^ 2 < Real.pi ^ 2 / 8 := by
    have hroot : 1 + eta < Real.sqrt ((Real.pi ^ 2 / 2) /
        (q₁ * factor ^ 2)) := by
      dsimp [etaLimit] at hetaLimit'
      linarith
    have hrootPos : 0 < Real.sqrt ((Real.pi ^ 2 / 2) /
        (q₁ * factor ^ 2)) := Real.sqrt_pos.2
      (div_pos (by positivity)
        (mul_pos hq₁pos (sq_pos_of_pos hfactorPos)))
    have hsquare : (Real.sqrt ((Real.pi ^ 2 / 2) /
        (q₁ * factor ^ 2))) ^ 2 =
          (Real.pi ^ 2 / 2) / (q₁ * factor ^ 2) :=
      Real.sq_sqrt (div_nonneg (by positivity)
        (mul_nonneg hq₁pos.le (sq_nonneg factor)))
    have hprod : q₁ * factor ^ 2 * (1 + eta) ^ 2 < Real.pi ^ 2 / 2 := by
      have hmul := mul_lt_mul_of_pos_left
        ((sq_lt_sq₀ (show (0 : ℝ) ≤ 1 + eta by positivity)
          (show (0 : ℝ) ≤ Real.sqrt ((Real.pi ^ 2 / 2) /
            (q₁ * factor ^ 2)) by positivity)).2 hroot)
        (mul_pos hq₁pos (sq_pos_of_pos hfactorPos))
      have heq : q₁ * factor ^ 2 *
          ((Real.pi ^ 2 / 2) / (q₁ * factor ^ 2)) = Real.pi ^ 2 / 2 := by
        field_simp [ne_of_gt hq₁pos, ne_of_gt hfactorPos]
      nlinarith [hmul]
    dsimp [beta]
    nlinarith [hprod]
  have hrateLimit : q₁ * beta ^ 2 / (Real.pi ^ 2 / 2) < (1 / 4 : ℝ) := by
    apply (div_lt_iff₀ hpi).2
    calc
      q₁ * beta ^ 2 < Real.pi ^ 2 / 8 := hqbeta
      _ = (1 / 4 : ℝ) * (Real.pi ^ 2 / 2) := by ring
  obtain ⟨n, hn⟩ := (tendsto_rangeCoverEnergy_atTop.eventually
    (Ioi_mem_nhds hrateLimit)).exists
  let k : ℕ := n + 1
  have hk : 0 < k := by dsimp [k]; omega
  have henergy : q₁ * beta ^ 2 <
      (Real.pi ^ 2 / 2) * (rangeCoverUnion k hk).realEnergy := by
    have h := hn
    have h' : q₁ * beta ^ 2 / (Real.pi ^ 2 / 2) <
        (rangeCoverUnion k hk).realEnergy := by
      simpa [k] using h
    simpa [mul_comm] using (div_lt_iff₀ hpi).1 h'
  let rangeRate : ℝ := q₁ * beta ^ 2
  have hrangeRate : 0 < rangeRate := mul_pos hq₁pos (sq_pos_of_pos hbetaPos)
  have hrangeRateLt : rangeRate < (Real.pi ^ 2 / 2) *
      (rangeCoverUnion k hk).realEnergy := by simpa [rangeRate] using henergy
  have htargetRate : 0 < q₀ := hq₀
  have hgap : q₀ < rangeRate / beta ^ 2 := by
    dsimp [rangeRate]
    rw [mul_div_cancel_right₀ q₁ (pow_ne_zero 2 hbetaPos.ne')]
    exact hq₁
  have hmargin : a + zeta < (q₀ * sigma ^ 2) * t / b ^ 2 := by
    dsimp [q₀]
    have hq : q₀ * sigma ^ 2 = d := by
      dsimp [q₀]
      field_simp [ne_of_gt hsigmaSq]
    rw [hq]
    have hstrict : epsilon < d * t / b ^ 2 - (a + zeta) := hepsilonMargin
    linarith
  refine ⟨b, factor, eta, rangeRate, q₀, k, hk,
    hb, hfactor, heta, hrangeRate, hrangeRateLt, htargetRate, ?_, hbin, hmargin⟩
  simpa [beta] using hgap

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

end

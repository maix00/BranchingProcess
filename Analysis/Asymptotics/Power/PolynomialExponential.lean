/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Absorbing a polynomial entrance cost into an exponential budget

The public theorem in this file is:

- `Asymptotics.eventually_exp_neg_horizon_le_polynomial`:
  for $C,\delta,\varepsilon>0$ and $p\in\mathbb R$, sufficiently large $\Delta$, and
  $L\ge\lfloor\Delta^{2+\varepsilon}\rfloor$,
  $\exp(-\delta L/\Delta^2)\le C/\Delta^p$.

This is the deterministic comparison following the entrance estimate in
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (master's thesis, Fudan University, 2026), Chapter 3, proof of
Lemma 3.5.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Asymptotics

/-- An exponential in a positive power eventually dominates every prescribed
inverse power. -/
private theorem eventually_exp_neg_rpow_le_div_rpow
    {a b C p : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 < C) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-a * x ^ b) ≤ C / x ^ p := by
  have hlittleBase :=
    (isLittleO_exp_neg_mul_rpow_atTop ha (-p / b)).comp_tendsto
      (_root_.tendsto_rpow_atTop hb)
  have hpow : (fun x : ℝ => (x ^ b) ^ (-p / b)) =ᶠ[atTop]
      fun x => x ^ (-p) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_mul (le_of_lt hx)]
    congr 1
    field_simp [ne_of_gt hb]
  have hlittle : (fun x : ℝ => Real.exp (-a * x ^ b)) =o[atTop]
      fun x => x ^ (-p) :=
    hlittleBase.congr' EventuallyEq.rfl hpow
  have hratio := hlittle.tendsto_div_nhds_zero
  have hsmall := hratio.eventually (Iio_mem_nhds hC)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsmall] with x hx hsmall
  have hdenom : x ^ (-p) = (x ^ p)⁻¹ :=
    Real.rpow_neg (le_of_lt hx) p
  have hratioEq : Real.exp (-a * x ^ b) / x ^ (-p) =
      Real.exp (-a * x ^ b) * x ^ p := by
    rw [hdenom]
    simp
  rw [hratioEq] at hsmall
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hx p)]
  exact le_of_lt hsmall

/-- The polynomial cost $C\Delta^{-p}$ of the entrance step in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(master's thesis, Fudan University, 2026), Chapter 3, proof of Lemma 3.5,
is absorbed by the exponential budget once
$L\ge\lfloor\Delta^{2+\varepsilon}\rfloor$. -/
theorem eventually_exp_neg_horizon_le_polynomial
    {C δ ε p : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ Delta : ℝ in atTop,
      ∀ L : ℕ, Nat.floor (Delta ^ (2 + ε)) ≤ L →
        Real.exp (-δ * (L : ℝ) / Delta ^ (2 : ℝ)) ≤
          C / Delta ^ p := by
  have hsmallExp := eventually_exp_neg_rpow_le_div_rpow
    (C := C) (a := δ / 2) (b := ε) (p := p) (by linarith) hε hC
  have hlargePower :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 2 + ε)).eventually
      (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hsmallExp, eventually_ge_atTop (2 : ℝ), hlargePower]
    with Delta hsmallExp hDelta hlargePower
  intro L hL
  have hDeltaPos : 0 < Delta := by linarith
  have hwidthPower : Delta ^ (2 + ε) = Delta ^ (2 : ℝ) * Delta ^ ε :=
    Real.rpow_add hDeltaPos 2 ε
  have hfloorLower : Delta ^ (2 + ε) / 2 ≤
      (Nat.floor (Delta ^ (2 + ε)) : ℝ) := by
    have hfloor : Delta ^ (2 + ε) <
        (Nat.floor (Delta ^ (2 + ε)) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    nlinarith [hlargePower]
  have hfloorLeL : (Nat.floor (Delta ^ (2 + ε)) : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast hL
  have htime : Delta ^ ε / 2 ≤ (L : ℝ) / Delta ^ (2 : ℝ) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
      (Real.rpow_pos_of_pos hDeltaPos 2)]
    nlinarith [hfloorLower.trans hfloorLeL, hwidthPower]
  have hexponent : -δ * (L : ℝ) / Delta ^ (2 : ℝ) ≤
      -(δ / 2) * Delta ^ ε := by
    have hmul := mul_le_mul_of_nonneg_left htime hδ.le
    calc
      -δ * (L : ℝ) / Delta ^ (2 : ℝ) =
          -(δ * ((L : ℝ) / Delta ^ (2 : ℝ))) := by
        field_simp [ne_of_gt (Real.rpow_pos_of_pos hDeltaPos 2)]
      _ ≤ -(δ * (Delta ^ ε / 2)) := neg_le_neg hmul
      _ = -(δ / 2) * Delta ^ ε := by ring
  exact (Real.exp_le_exp.mpr hexponent).trans hsmallExp

end Asymptotics

end

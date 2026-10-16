/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.RegularVariation.Basic

/-!
# Polynomial lower bounds for decreasing regularly varying functions

The public theorem in this file is:

- Asymptotics.IsRegularlyVaryingAtTop.exists_eventually_lower_power_of_inverse_monotone:
  if $f$ has index $-\rho$, $\rho\ge0$, and $1/f$ is eventually
  nondecreasing, then for every $\varepsilon>0$ there is $C>0$ with
  $f(x)\ge C/x^{\rho+\varepsilon}$ for all sufficiently large $x$.

This is the Potter-bound consequence used after the survival asymptotic in
Wang Yiyang, *Asymptotic speed of the $N$-branching random walk with infinite
offspring*, Appendix A.2, first lemma. The analytic input is the monotone
Potter bound in Bingham, Goldie and Teugels, *Regular Variation*,
Theorem 1.5.6 (Cambridge University Press, 1989, MR1015093).
-/

@[expose] public section

open Filter
open scoped Topology

namespace Asymptotics.IsRegularlyVaryingAtTop

/-- A positive eventually decreasing regularly varying function with index
$-\rho$ dominates every lower power $x^{-\rho-\varepsilon}$. This is the
Potter step used for the survival probability in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Appendix A.2, first lemma. -/
theorem exists_eventually_lower_power_of_inverse_monotone
    {f : ℝ → ℝ} {ρ : ℝ}
    (hreg : IsRegularlyVaryingAtTop f (-ρ))
    (hmono : IsEventuallyMonotoneAtTop (fun x => (f x)⁻¹))
    (hρ : 0 ≤ ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      C / x ^ (ρ + ε) ≤ f x := by
  have hrec : IsRegularlyVaryingAtTop (fun x => (f x)⁻¹) ρ := by
    simpa using hreg.inv
  obtain ⟨Rpot, hRpot, hpot⟩ :=
    hrec.exists_potter_upper_bound hmono hρ hε
  obtain ⟨Rpos, hRpos⟩ := eventually_atTop.1 hreg.eventually_pos
  let R : ℝ := max Rpot (max Rpos 1)
  have hRpot' : Rpot ≤ R := le_max_left _ _
  have hRpos' : Rpos ≤ R :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hRone : 1 ≤ R :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hRpositive : 0 < R := by linarith
  have hfR : 0 < f R := hRpos R hRpos'
  let p : ℝ := ρ + ε
  let K : ℝ := 2 ^ p
  have hK : 0 < K := Real.rpow_pos_of_pos (by norm_num) p
  have hRpow : 0 < R ^ p := Real.rpow_pos_of_pos hRpositive p
  let C : ℝ := f R * R ^ p / K
  have hC : 0 < C := div_pos (mul_pos hfR hRpow) hK
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop R] with x hx
  have hfx : 0 < f x := hRpos x (hRpos'.trans hx)
  have hxpos : 0 < x := lt_of_lt_of_le hRpositive hx
  have hxpow : 0 < x ^ p := Real.rpow_pos_of_pos hxpos p
  have hratio := hpot (x := R) (y := x) hRpot' hx
  have hpowRatio : (x / R) ^ p = x ^ p / R ^ p :=
    Real.div_rpow (le_of_lt hxpos) (le_of_lt hRpositive) p
  change (f x)⁻¹ / (f R)⁻¹ ≤ K * (x / R) ^ p at hratio
  rw [hpowRatio] at hratio
  have hratio' : f R / f x ≤ K * (x ^ p / R ^ p) := by
    simpa [div_inv_eq_mul, div_eq_mul_inv, mul_comm] using hratio
  have hfirst : f R ≤ K * (x ^ p / R ^ p) * f x :=
    (div_le_iff₀ hfx).1 hratio'
  have hsecond : f R * R ^ p ≤ f x * K * x ^ p := by
    calc
      f R * R ^ p ≤ (K * (x ^ p / R ^ p) * f x) * R ^ p :=
        mul_le_mul_of_nonneg_right hfirst hRpow.le
      _ = f x * K * x ^ p := by
        field_simp [ne_of_gt hRpow]
  have hproduct : C ≤ f x * x ^ p := by
    dsimp [C]
    apply (div_le_iff₀ hK).2
    nlinarith [hsecond]
  exact (div_le_iff₀ hxpow).2 hproduct

end Asymptotics.IsRegularlyVaryingAtTop

end

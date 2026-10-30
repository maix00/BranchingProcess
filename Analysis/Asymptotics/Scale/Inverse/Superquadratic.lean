/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Analysis.Asymptotics.Scale.Inverse.Basic
public import Analysis.Asymptotics.Scale.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Analysis.Asymptotics.Sequence.SqrtRatio
/-!
# Superquadratic scales and their inverse widths

## Public declarations

`IsSuperquadraticScale L` means that for every `K : ℕ`, eventually
`K * δ^2 ≤ L δ`. It implies `δ^2 / (L δ + 1) → 0`. For a time scale tending
to infinity, both generalized inverse widths satisfy `inverseWidth^2 / n → 0`
and `inverseWidth / √n → 0`; each is an `IsSmallDeviationScale` with
normalization `√n`.

The public declarations are `Asymptotics.IsSuperquadraticScale`,
`Asymptotics.tendsto_width_sq_div_shiftedScale_of_superquadratic`,
`Asymptotics.eventually_mul_sq_inverseScale_le_four_mul`,
`Asymptotics.eventually_mul_sq_inverseScale_le_four_mul_of_superquadratic`,
`Asymptotics.tendsto_sq_inverseScale_div_atTop_zero`,
`Asymptotics.tendsto_sq_natCast_div_atTop_zero_of_eventually_mul_sq_le`,
`Asymptotics.eventually_mul_sq_upperInverseScale_le_eight_mul`,
`Asymptotics.tendsto_sq_upperInverseScale_div_atTop_zero`,
`Asymptotics.tendsto_inverseScale_div_sqrt_atTop_zero`,
`Asymptotics.tendsto_upperInverseScale_div_sqrt_atTop_zero`,
`Asymptotics.isSmallDeviationScale_inverseScale`, and
`Asymptotics.isSmallDeviationScale_upperInverseScale`.
-/

public section

open Filter
open scoped BigOperators

namespace Asymptotics

/-- An integer time scale eventually dominates every constant multiple of the
square of its width. This order-theoretic form avoids casts and is equivalent
to the usual assertion `L δ / δ² → ∞`. -/
def IsSuperquadraticScale (L : ℕ → ℕ) : Prop :=
  ∀ K : ℕ, Filter.Eventually (fun δ => K * δ ^ 2 ≤ L δ) atTop

/-- Along a superquadratic time scale, the squared width is negligible even
when the time is shifted by a fixed nonnegative amount. -/
theorem tendsto_width_sq_div_shiftedScale_of_superquadratic
    {L : ℕ → ℕ} (hquadratic : IsSuperquadraticScale L) :
    Tendsto (fun δ : ℕ => (δ : ℝ) ^ 2 / ((L δ : ℝ) + 1)) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (2 / ε)
  have hKpos : 0 < (K : ℝ) := by
    exact lt_trans (by positivity : (0 : ℝ) < 2 / ε) hK
  have hKbound : 1 / (K : ℝ) < ε := by
    have hK' : 2 < (K : ℝ) * ε := by
      simpa [mul_comm] using (div_lt_iff₀ hε).mp hK
    rw [div_lt_iff₀ hKpos]
    nlinarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hquadratic K)
  refine ⟨N, ?_⟩
  intro δ hNδ
  have hδreal : (K : ℝ) * (δ : ℝ) ^ 2 ≤ (L δ : ℝ) := by
    exact_mod_cast hN δ hNδ
  have hratio : (δ : ℝ) ^ 2 / ((L δ : ℝ) + 1) ≤ 1 / (K : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < (L δ : ℝ) + 1)).2
    rw [one_div, mul_comm]
    apply (le_div_iff₀ hKpos).2
    nlinarith [hδreal]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
  exact hratio.trans_lt hKbound

/-- A superquadratic lower bound on the original scale gives the corresponding
subdiffusive bound on its generalized inverse. This is the integer core of the
implication `x(n) / sqrt n → 0`: the factor four comes from
`x(n) ≤ 2 * (x(n) - 1)`. -/
theorem eventually_mul_sq_inverseScale_le_four_mul
    {L : ℕ → ℕ} (hL : Tendsto L atTop atTop) (K : ℕ)
    (hquadratic : Filter.Eventually (fun δ => K * δ ^ 2 ≤ L δ) atTop) :
    Filter.Eventually (fun n => K * (inverseScale L n) ^ 2 ≤ 4 * n) atTop := by
  obtain ⟨D, hD⟩ := eventually_atTop.1 hquadratic
  filter_upwards [tendsto_atTop.1 (tendsto_inverseScale_atTop hL)
    (max (D + 1) 2)] with n hn
  let x := inverseScale L n
  let k := x - 1
  have hxD : D + 1 ≤ x := le_trans (le_max_left (D + 1) 2) hn
  have hx2 : 2 ≤ x := le_trans (le_max_right (D + 1) 2) hn
  have hkD : D ≤ k := by
    dsimp [k]
    omega
  have hK : K * k ^ 2 ≤ L k := hD k hkD
  have hpred : L k + 1 < n := by
    dsimp [k, x]
    apply scale_pred_inverseScale_add_one_lt
    exact lt_of_lt_of_le (by omega : 0 < max (D + 1) 2) hn
  have hxk : x ≤ 2 * k := by
    dsimp [k]
    omega
  calc
    K * x ^ 2 ≤ K * (2 * k) ^ 2 :=
      Nat.mul_le_mul_left K (Nat.pow_le_pow_left hxk 2)
    _ = 4 * (K * k ^ 2) := by ring
    _ ≤ 4 * L k := Nat.mul_le_mul_left 4 hK
    _ ≤ 4 * n := Nat.mul_le_mul_left 4
      (Nat.le_of_lt (lt_trans (Nat.lt_succ_self (L k)) hpred))

/-- Uniform form of the inverse subdiffusive estimate for a superquadratic
scale. -/
theorem eventually_mul_sq_inverseScale_le_four_mul_of_superquadratic
    {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hquadratic : IsSuperquadraticScale L) (K : ℕ) :
    Filter.Eventually (fun n => K * (inverseScale L n) ^ 2 ≤ 4 * n) atTop :=
  eventually_mul_sq_inverseScale_le_four_mul hL K (hquadratic K)

/-- The squared generalized inverse is negligible compared with time. -/
theorem tendsto_sq_inverseScale_div_atTop_zero
    {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hquadratic : IsSuperquadraticScale L) :
    Tendsto (fun n : ℕ =>
      ((inverseScale L n : ℝ) ^ 2) / (n : ℝ)) atTop (nhds 0) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (4 / ε)
  have hKpos : 0 < (K : ℝ) := by
    exact lt_of_le_of_lt (div_nonneg (by norm_num) hε.le) hK
  have hfour : (4 : ℝ) / K < ε := by
    rw [div_lt_iff₀ hKpos]
    simpa [mul_comm] using (div_lt_iff₀ hε).mp hK
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (eventually_mul_sq_inverseScale_le_four_mul_of_superquadratic
      hL hquadratic K)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left N 1) hn
  have hnposNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one
    (le_trans (le_max_right N 1) hn)
  have hbound := hN n hnN
  have hboundReal :
      (K : ℝ) * (inverseScale L n : ℝ) ^ 2 ≤ 4 * (n : ℝ) := by
    exact_mod_cast hbound
  have hxbound :
      (inverseScale L n : ℝ) ^ 2 ≤ 4 * (n : ℝ) / K := by
    rw [le_div_iff₀ hKpos]
    simpa [mul_comm] using hboundReal
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
  have hratio :
      (inverseScale L n : ℝ) ^ 2 / (n : ℝ) ≤ 4 / K := by
    rw [div_le_iff₀ hnpos]
    calc
      (inverseScale L n : ℝ) ^ 2 ≤ 4 * (n : ℝ) / K := hxbound
      _ = (4 / K) * n := by ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (div_nonneg (sq_nonneg _) hnpos.le)]
  exact hratio.trans_lt hfour

/-- A uniform quadratic bound with an arbitrary fixed linear coefficient
implies that a natural-valued sequence is subdiffusive. This form is useful
for both generalized inverses and their shifted variants. -/
theorem tendsto_sq_natCast_div_atTop_zero_of_eventually_mul_sq_le
    {f : ℕ → ℕ} {C : ℕ}
    (hbound : ∀ K : ℕ,
      Filter.Eventually (fun n => K * f n ^ 2 ≤ C * n) atTop) :
    Tendsto (fun n : ℕ => ((f n : ℝ) ^ 2) / (n : ℝ)) atTop (nhds 0) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt ((C : ℝ) / ε)
  have hKpos : 0 < (K : ℝ) := by
    exact lt_of_le_of_lt (div_nonneg (Nat.cast_nonneg _) hε.le) hK
  have hCbound : (C : ℝ) / K < ε := by
    rw [div_lt_iff₀ hKpos]
    simpa [mul_comm] using (div_lt_iff₀ hε).mp hK
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hbound K)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left N 1) hn
  have hnposNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one
    (le_trans (le_max_right N 1) hn)
  have hboundN := hN n hnN
  have hboundReal :
      (K : ℝ) * (f n : ℝ) ^ 2 ≤ (C : ℝ) * (n : ℝ) := by
    exact_mod_cast hboundN
  have hxbound :
      (f n : ℝ) ^ 2 ≤ (C : ℝ) * (n : ℝ) / K := by
    rw [le_div_iff₀ hKpos]
    simpa [mul_comm] using hboundReal
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
  have hratio :
      (f n : ℝ) ^ 2 / (n : ℝ) ≤ (C : ℝ) / K := by
    rw [div_le_iff₀ hnpos]
    calc
      (f n : ℝ) ^ 2 ≤ (C : ℝ) * (n : ℝ) / K := hxbound
      _ = ((C : ℝ) / K) * n := by ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (div_nonneg (sq_nonneg _) hnpos.le)]
  exact hratio.trans_lt hCbound

/-- The upper generalized inverse inherits the subdiffusive bound from a
superquadratic scale. The shift from `n` to `n + 1` changes only the uniform
constant in the quadratic estimate. -/
theorem eventually_mul_sq_upperInverseScale_le_eight_mul
    {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hquadratic : IsSuperquadraticScale L) (K : ℕ) :
    Filter.Eventually
      (fun n => K * (upperInverseScale L n) ^ 2 ≤ 8 * n) atTop := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (eventually_mul_sq_inverseScale_le_four_mul_of_superquadratic
      hL hquadratic K)
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hnN : N ≤ n := le_trans (le_max_left N 1) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hupper : upperInverseScale L n ≤ inverseScale L (n + 1) := by
    simp only [upperInverseScale]
    omega
  have hnext := hN (n + 1) (by omega)
  calc
    K * (upperInverseScale L n) ^ 2 ≤
        K * (inverseScale L (n + 1)) ^ 2 :=
      Nat.mul_le_mul_left K (Nat.pow_le_pow_left hupper 2)
    _ ≤ 4 * (n + 1) := by simpa using hnext
    _ ≤ 8 * n := by omega

/-- The squared upper generalized inverse is negligible compared with time. -/
theorem tendsto_sq_upperInverseScale_div_atTop_zero
    {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hquadratic : IsSuperquadraticScale L) :
    Tendsto (fun n : ℕ => ((upperInverseScale L n : ℝ) ^ 2) / (n : ℝ))
      atTop (nhds 0) :=
  tendsto_sq_natCast_div_atTop_zero_of_eventually_mul_sq_le
    (fun K => eventually_mul_sq_upperInverseScale_le_eight_mul
      hL hquadratic K)

/-- The inverse scale in a superquadratic regime is negligible relative to
the square-root time scale. -/
theorem tendsto_inverseScale_div_sqrt_atTop_zero
    {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hquadratic : IsSuperquadraticScale L) :
    Tendsto (fun n : ℕ => (inverseScale L n : ℝ) / Real.sqrt (n : ℝ))
      atTop (nhds 0) :=
  tendsto_div_sqrt_atTop_zero_of_tendsto_sq_div_atTop_zero
    (fun n => Nat.cast_nonneg (inverseScale L n))
    (by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      exact_mod_cast hn)
    (tendsto_sq_inverseScale_div_atTop_zero hL hquadratic)

/-- The upper inverse scale in a superquadratic regime is negligible relative
to the square-root time scale. -/
theorem tendsto_upperInverseScale_div_sqrt_atTop_zero
    {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hquadratic : IsSuperquadraticScale L) :
    Tendsto (fun n : ℕ => (upperInverseScale L n : ℝ) / Real.sqrt (n : ℝ))
      atTop (nhds 0) :=
  tendsto_div_sqrt_atTop_zero_of_tendsto_sq_div_atTop_zero
    (fun n => Nat.cast_nonneg (upperInverseScale L n))
    (by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      exact_mod_cast hn)
    (tendsto_sq_upperInverseScale_div_atTop_zero hL hquadratic)

/-- Package the generalized inverse as a small-deviation scale with the
diffusive normalization `sqrt n`. -/
theorem isSmallDeviationScale_inverseScale
    {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hquadratic : IsSuperquadraticScale L) :
    IsSmallDeviationScale (fun n => (inverseScale L n : ℝ))
      (fun n => Real.sqrt (n : ℝ)) := by
  apply IsSmallDeviationScale.of_tendsto
  · simpa only [Function.comp_def] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ))
        atTop atTop).comp (tendsto_inverseScale_atTop hL)
  · exact tendsto_inverseScale_div_sqrt_atTop_zero hL hquadratic

/-- Package the upper generalized inverse as a small-deviation scale with
the diffusive normalization `sqrt n`. -/
theorem isSmallDeviationScale_upperInverseScale
    {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hquadratic : IsSuperquadraticScale L) :
    IsSmallDeviationScale (fun n => (upperInverseScale L n : ℝ))
      (fun n => Real.sqrt (n : ℝ)) := by
  apply IsSmallDeviationScale.of_tendsto
  · simpa only [Function.comp_def] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ))
        atTop atTop).comp (tendsto_upperInverseScale_atTop hL)
  · exact tendsto_upperInverseScale_div_sqrt_atTop_zero hL hquadratic

end Asymptotics

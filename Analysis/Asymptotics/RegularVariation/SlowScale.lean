/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.RegularVariation.Basic
public import Analysis.Asymptotics.Scale.SlowDiagonal

/-!
# Slowly growing multipliers for regularly varying functions

The public theorems are:

- `exists_tendsto_slowScale_of_eventually`: if $f$ has regular variation
  index $\rho$, $x_n\to\infty$, $r_n\to0$ with $r_n\ge0$ eventually, and
  each predicate $P(k,n)$ holds eventually for every fixed $k$, then there is
  a monotone integer scale $d_n\to\infty$ such that $P(d_n+1,n)$ holds
  eventually, $(d_n+1)r_n\to0$, and
  $\frac{f((d_n+1)x_n)}{f(x_n)}(d_n+1)^{-\rho}\to1$.
- `exists_tendsto_slowScale`: under the same scale and error assumptions but
  without $P$, there is a monotone real scale $a_n\to\infty$ such that
  $a_nr_n\to0$ and $\frac{f(a_nx_n)}{f(x_n)}a_n^{-\rho}\to1$.

For a regularly varying function, each fixed positive multiplier has the
usual ratio limit. A diagonal choice lets the multiplier tend to infinity
while preserving that ratio limit and any separately prescribed vanishing
product constraint.
-/

open Filter
open scoped Topology

@[expose] public section

namespace Asymptotics.IsRegularlyVaryingAtTop

/-- Choose one slowly diverging multiplier that preserves both fixed-parameter
eventual properties and the regular-variation ratio limit. The same diagonal
also makes its product with a nonnegative error scale tend to zero.

The natural parameter `d` is shifted by one to form the positive real
multiplier `d + 1`. This is a diagonal argument, not uniform convergence for
unbounded multipliers. -/
theorem exists_tendsto_slowScale_of_eventually
    {f : ℝ → ℝ} {ρ : ℝ} {x r : ℕ → ℝ} {P : ℕ → ℕ → Prop}
    (hreg : IsRegularlyVaryingAtTop f ρ)
    (hx : Tendsto x atTop atTop)
    (hr : Tendsto r atTop (nhds 0))
    (hr_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ r n)
    (hP : ∀ k, ∀ᶠ n : ℕ in atTop, P k n) :
    ∃ d : ℕ → ℕ, Monotone d ∧ Tendsto d atTop atTop ∧
      (∀ᶠ n : ℕ in atTop, P (d n + 1) n) ∧
      Tendsto (fun n => ((d n : ℝ) + 1) * r n) atTop (nhds 0) ∧
      Tendsto (fun n =>
        (f (((d n : ℝ) + 1) * x n) / f (x n)) / (((d n : ℝ) + 1) ^ ρ))
          atTop (nhds 1) := by
  let approximation : ℕ → ℕ → Prop := fun k n =>
    |(f ((((k + 1 : ℕ) : ℝ) * x n)) / f (x n)) /
        (((k + 1 : ℕ) : ℝ) ^ ρ) - 1| < 1 / ((k + 1 : ℕ) : ℝ)
  have happ : ∀ k, ∀ᶠ n : ℕ in atTop, approximation k n := by
    intro k
    let c : ℝ := ((k + 1 : ℕ) : ℝ)
    have hc : 0 < c := by positivity
    have hlimit : Tendsto
        (fun n : ℕ => f (c * x n) / f (x n) / (c ^ ρ)) atTop (nhds 1) := by
      have hratio : Tendsto (fun n : ℕ => f (c * x n) / f (x n))
          atTop (nhds (c ^ ρ)) := (hreg.ratio_tendsto hc).comp hx
      have hpow : 0 < c ^ ρ := Real.rpow_pos_of_pos hc ρ
      simpa [div_self hpow.ne'] using hratio.div_const (c ^ ρ)
    have hclose : ∀ᶠ n : ℕ in atTop,
        |(f (c * x n) / f (x n)) / (c ^ ρ) - 1| < 1 / c := by
      have hball := hlimit.eventually
        (Metric.ball_mem_nhds 1 (by positivity : (0 : ℝ) < 1 / c))
      filter_upwards [hball] with n hn
      simpa only [Real.dist_eq, abs_sub_comm] using hn
    filter_upwards [hclose] with n hn
    simpa [approximation, c] using hn
  have hproperty : ∀ k, ∀ᶠ n : ℕ in atTop,
      P (k + 1) n ∧ approximation k n := by
    intro k
    exact (hP (k + 1)).and (happ k)
  obtain ⟨d, hdmono, hd, hdiag, hproduct⟩ :=
    Asymptotics.exists_tendsto_slowDiagonal_mul_tendsto_zero
      hproperty hr hr_nonneg
  have hPdiag : ∀ᶠ n : ℕ in atTop, P (d n + 1) n :=
    hdiag.mono fun n hn => hn.1
  let a : ℕ → ℝ := fun n => (d n : ℝ) + 1
  have hdiagBound : ∀ᶠ n : ℕ in atTop,
      |(f (a n * x n) / f (x n)) / (a n ^ ρ) - 1| < (a n)⁻¹ := by
    filter_upwards [hdiag] with n hn
    simpa [approximation, a, Nat.cast_add, Nat.cast_one, one_div] using hn.2
  have hinv : Tendsto (fun n => (a n)⁻¹) atTop (nhds 0) := by
    have hcast : Tendsto (fun n : ℕ => (d n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hd
    have ha : Tendsto a atTop atTop := by
      simpa [a] using tendsto_atTop_add_const_right atTop 1 hcast
    exact tendsto_inv_atTop_zero.comp ha
  have har : Tendsto (fun n => a n * r n) atTop (nhds 0) := by
    simpa [a, add_mul] using hproduct.add hr
  have hratio : Tendsto
      (fun n => (f (a n * x n) / f (x n)) / (a n ^ ρ)) atTop (nhds 1) := by
    rw [tendsto_iff_dist_tendsto_zero, Metric.tendsto_nhds]
    intro ε hε
    have hsmall : ∀ᶠ n : ℕ in atTop, (a n)⁻¹ < ε :=
      hinv.eventually (Iio_mem_nhds hε)
    filter_upwards [hdiagBound, hsmall] with n hbound hsmall
    simpa [Real.dist_eq, abs_sub_comm] using lt_trans hbound hsmall
  exact ⟨d, hdmono, hd, hPdiag, har, hratio⟩

/-- A slowly growing positive multiplier preserves a regular-variation ratio
limit along any argument tending to infinity, while its product with a
nonnegative error scale tends to zero. -/
theorem exists_tendsto_slowScale
    {f : ℝ → ℝ} {ρ : ℝ} {x r : ℕ → ℝ}
    (hreg : IsRegularlyVaryingAtTop f ρ)
    (hx : Tendsto x atTop atTop)
    (hr : Tendsto r atTop (nhds 0))
    (hr_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ r n) :
    ∃ a : ℕ → ℝ, Monotone a ∧ Tendsto a atTop atTop ∧
      Tendsto (fun n => a n * r n) atTop (nhds 0) ∧
      Tendsto (fun n => (f (a n * x n) / f (x n)) / (a n ^ ρ))
        atTop (nhds 1) := by
  obtain ⟨d, hdmono, hd, -, hproduct, hratio⟩ :=
    hreg.exists_tendsto_slowScale_of_eventually hx hr hr_nonneg
      (fun _ => Filter.Eventually.of_forall fun _ => trivial)
  let a : ℕ → ℝ := fun n => (d n : ℝ) + 1
  have hamono : Monotone a := by
    intro i j hij
    simpa [a, add_comm] using
      (add_le_add_right (Nat.cast_le.mpr (hdmono hij)) (1 : ℝ))
  have ha : Tendsto a atTop atTop := by
    have hcast : Tendsto (fun n : ℕ => (d n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hd
    simpa [a] using tendsto_atTop_add_const_right atTop 1 hcast
  have hproduct' : Tendsto (fun n => a n * r n) atTop (nhds 0) := by
    simpa [a] using hproduct
  have hratio' : Tendsto
      (fun n => (f (a n * x n) / f (x n)) / (a n ^ ρ)) atTop (nhds 1) := by
    simpa [a] using hratio
  exact ⟨a, hamono, ha, hproduct', hratio'⟩

end Asymptotics.IsRegularlyVaryingAtTop

end

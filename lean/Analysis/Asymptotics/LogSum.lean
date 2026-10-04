/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.NegativeRatio
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithms of finite sums at a diverging negative scale

A finite sum changes a logarithmic ratio by only a vanishing additive term.
This estimate is independent of probability and path-space structure.
-/

@[expose] public section

namespace Asymptotics

open Filter
open scoped Topology

/-- If each summand has logarithmic ratio at least `1 - η`, then a finite
sum has ratio at least `1 - η - δ` eventually. The only extra cost is the
logarithm of the fixed number of summands. -/
theorem eventually_one_sub_eta_sub_delta_le_log_sum_ratio
    {ι I : Type*} [DecidableEq ι] {l : Filter I}
    (F : Finset ι) (hF : 0 < F.card)
    (g q : I → ℝ) (p : I → ι → ℝ)
    (η δ : ℝ) (hδ : 0 < δ)
    (hg : Tendsto g l atBot)
    (hqpos : ∀ᶠ x in l, 0 < q x)
    (hsum : ∀ᶠ x in l, q x ≤ ∑ i ∈ F, p x i)
    (hp : ∀ i ∈ F, ∀ᶠ x in l, 0 < p x i)
    (hlog : ∀ i ∈ F, ∀ᶠ x in l,
      1 - η ≤ Real.log (p x i) / g x) :
    ∀ᶠ x in l, 1 - η - δ ≤ Real.log (q x) / g x := by
  have hneg : ∀ᶠ x in l, g x < 0 :=
    hg.eventually (eventually_lt_atBot 0)
  have hterms : ∀ᶠ x in l, ∀ i ∈ F,
      0 < p x i ∧ 1 - η ≤ Real.log (p x i) / g x := by
    apply F.eventually_all.2
    intro i hi
    exact (hp i hi).and (hlog i hi)
  let C : ℝ := Real.log (F.card : ℝ)
  have hC : 0 < (F.card : ℝ) := Nat.cast_pos.mpr hF
  have herror : Tendsto (fun x => C / g x) l (𝓝 0) := by
    simpa [C, div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_inv_atBot_zero.comp hg) :
        Tendsto (fun x => C * (g x)⁻¹) l (𝓝 (C * 0)))
  have hsmall : ∀ᶠ x in l, -δ < C / g x :=
    herror.eventually (lt_mem_nhds (by linarith : -δ < (0 : ℝ)))
  filter_upwards [hneg, hqpos, hsum, hterms, hsmall] with x hxneg hqx hsumx htermsx herr
  have hterm (i : ι) (hi : i ∈ F) :
      p x i ≤ Real.exp ((1 - η) * g x) := by
    have ⟨hpi, hratio⟩ := htermsx i hi
    have hlogi : Real.log (p x i) ≤ (1 - η) * g x :=
      (le_div_iff_of_neg hxneg).mp hratio
    calc
      p x i = Real.exp (Real.log (p x i)) := (Real.exp_log hpi).symm
      _ ≤ Real.exp ((1 - η) * g x) := Real.exp_le_exp.mpr hlogi
  have hsumBound :
      (∑ i ∈ F, p x i) ≤ (F.card : ℝ) * Real.exp ((1 - η) * g x) := by
    calc
      (∑ i ∈ F, p x i) ≤ ∑ i ∈ F, Real.exp ((1 - η) * g x) :=
        Finset.sum_le_sum fun i hi => hterm i hi
      _ = (F.card : ℝ) * Real.exp ((1 - η) * g x) := by simp
  have hqBound : q x ≤ (F.card : ℝ) * Real.exp ((1 - η) * g x) :=
    hsumx.trans hsumBound
  have hlogBound := Real.log_le_log hqx hqBound
  rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at hlogBound
  have hdiv :
      (Real.log (F.card : ℝ) + (1 - η) * g x) / g x ≤
        Real.log (q x) / g x := by
    exact (div_le_div_right_of_neg hxneg).2 (by simpa [C, add_comm] using hlogBound)
  have hdivEq :
    (Real.log (F.card : ℝ) + (1 - η) * g x) / g x =
        1 - η + C / g x := by
    dsimp [C]
    field_simp [hxneg.ne]
    ring
  rw [hdivEq] at hdiv
  linarith

/-- A finite sum has the logarithmic rate of its slowest-decaying summand.
The rates are expressed relative to a common denominator tending to `-∞`;
the denominator's negativity reverses the order, so the relevant rate is the
minimum of the component limits. -/
theorem tendsto_log_finite_union_ratio
    {ι I : Type*} [DecidableEq ι] {l : Filter I}
    (F : Finset ι) (hF : F.Nonempty) (i₀ : ι) (hi₀ : i₀ ∈ F)
    (g q : I → ℝ) (p : I → ι → ℝ) (rate : ι → ℝ) (L : ℝ)
    (hg : Tendsto g l atBot)
    (hqpos : ∀ᶠ x in l, 0 < q x)
    (hupper : ∀ᶠ x in l, q x ≤ ∑ i ∈ F, p x i)
    (hlower : ∀ᶠ x in l, p x i₀ ≤ q x)
    (hp : ∀ i ∈ F, ∀ᶠ x in l, 0 < p x i)
    (hlog : ∀ i ∈ F,
      Tendsto (fun x => Real.log (p x i) / g x) l (𝓝 (rate i)))
    (hL : ∀ i ∈ F, L ≤ rate i)
    (hrate : rate i₀ = L) :
    Tendsto (fun x => Real.log (q x) / g x) l (𝓝 L) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro y hy
    let δ : ℝ := (L - y) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    let η : ℝ := 1 - L + δ / 2
    have hlogLower : ∀ i ∈ F, ∀ᶠ x in l,
        1 - η ≤ Real.log (p x i) / g x := by
      intro i hi
      have hnear := (hlog i hi).eventually
        (Ioi_mem_nhds (show rate i - δ / 2 < rate i by linarith))
      filter_upwards [hnear] with x hx
      have htarget : 1 - η = L - δ / 2 := by dsimp [η]; ring
      rw [htarget]
      have hrateLower : L - δ / 2 ≤ rate i - δ / 2 := by
        have := hL i hi
        linarith
      linarith
    have hsum := eventually_one_sub_eta_sub_delta_le_log_sum_ratio
      F hF.card_pos g q p η (δ / 2) (by positivity) hg hqpos hupper
      (fun i hi => hp i hi) hlogLower
    have hsum' : ∀ᶠ x in l, L - δ ≤ Real.log (q x) / g x := by
      filter_upwards [hsum] with x hx
      have heq : 1 - η - δ / 2 = L - δ := by dsimp [η]; ring
      rw [heq] at hx
      exact hx
    have hgap : y < L - δ := by dsimp [δ]; linarith
    filter_upwards [hsum'] with x hx
    exact lt_of_lt_of_le hgap hx
  · intro y hy
    have hnear := (hlog i₀ hi₀).eventually
      (Iio_mem_nhds (by rw [hrate]; exact hy))
    have hneg : ∀ᶠ x in l, g x < 0 := hg.eventually (eventually_lt_atBot 0)
    filter_upwards [hnear, hneg, hqpos, hp i₀ hi₀,
      hlower] with x hnearx hnegx hqx hpx hlowerx
    have hlogle : Real.log (p x i₀) ≤ Real.log (q x) :=
      Real.log_le_log hpx hlowerx
    have hquot : Real.log (q x) / g x ≤
        Real.log (p x i₀) / g x :=
      (div_le_div_right_of_neg hnegx).2 hlogle
    exact lt_of_le_of_lt hquot hnearx

end Asymptotics

end

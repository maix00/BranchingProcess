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

end Asymptotics

end

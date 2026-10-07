/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Comparing diverging negative functions

A fixed additive error becomes negligible in the ratio when the denominator
tends to negative infinity. This is the estimate behind the asymptotic
comparison convention for negative logarithmic probabilities.
-/

@[expose] public section

namespace Asymptotics

open Filter
open scoped Topology

theorem eventually_one_sub_le_ratio_of_additive_bound
    {I : Type*} {l : Filter I} {f g : I → ℝ} (C : ℝ)
    (hfg : f ≤ᶠ[l] fun x => g x + C)
    (hg : Tendsto g l atBot) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in l, 1 - ε ≤ f x / g x := by
  have hneg : ∀ᶠ x in l, g x < 0 :=
    hg.eventually (eventually_lt_atBot 0)
  have herror : Tendsto (fun x => C / g x) l (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_inv_atBot_zero.comp hg) :
        Tendsto (fun x => C * (g x)⁻¹) l (𝓝 (C * 0)))
  have hsmall : ∀ᶠ x in l, -ε < C / g x :=
    herror.eventually (lt_mem_nhds (by linarith : -ε < (0 : ℝ)))
  filter_upwards [hfg, hneg, hsmall] with x hbound hxneg hεx
  have hdiv : (g x + C) / g x ≤ f x / g x :=
    (div_le_div_right_of_neg hxneg).2 hbound
  have heq : (g x + C) / g x = 1 + C / g x := by
    field_simp [hxneg.ne]
  linarith

/-- A fixed multiplicative comparison of positive quantities becomes a
one-sided comparison of their logarithmic ratio when the denominator tends
to zero. The negative sign of `log q` is handled by the preceding additive
bound lemma. -/
theorem eventually_one_sub_le_log_ratio_of_mul_bound
    {I : Type*} {l : Filter I} {p q : I → ℝ} (C : ℝ) (hC : 0 < C)
    (hpq : p ≤ᶠ[l] fun x => C * q x)
    (hp : ∀ᶠ x in l, 0 < p x) (hq : ∀ᶠ x in l, 0 < q x)
    (hq0 : Tendsto q l (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in l, 1 - ε ≤ Real.log (p x) / Real.log (q x) := by
  let g : I → ℝ := fun x => Real.log (q x)
  have hqWithin : Tendsto q l (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hq0, hq⟩
  have hg : Tendsto g l atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hqWithin
  have hfg : (fun x => Real.log (p x)) ≤ᶠ[l]
      (fun x => g x + Real.log C) := by
    filter_upwards [hpq, hp, hq] with x hmul hp' hq'
    have hlog := Real.log_le_log hp' hmul
    have hlog' : Real.log (p x) ≤ Real.log (C * q x) := by
      exact hlog
    rw [Real.log_mul hC.ne' hq'.ne'] at hlog'
    simpa [g, add_comm] using hlog'
  simpa only [g] using
    eventually_one_sub_le_ratio_of_additive_bound (Real.log C) hfg hg ε hε

end Asymptotics

end

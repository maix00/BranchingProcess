module

public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.Ring.Real
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

end Asymptotics

end

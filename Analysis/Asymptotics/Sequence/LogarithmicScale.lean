/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithms of quantities with power growth

## Public declarations

- `Asymptotics.tendsto_log_add_one_div_scale_of_power_bound`: if $L\to+\infty$,
  $u\geq0$ eventually, $p>0$, and $u\leq C L^p$ eventually for some $C\geq0$, then
  $\log(u+1)/L\to0$.

The estimate records that logarithmic growth is negligible compared with a
diverging scale whenever the quantity has at most a fixed power growth in that
scale.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Asymptotics

/-- A quantity bounded by a fixed positive power of a diverging scale has a
negligible logarithmic count relative to that scale. -/
theorem tendsto_log_add_one_div_scale_of_power_bound
    {I : Type*} {l : Filter I} {u L : I → ℝ} {C p : ℝ}
    (hL : Tendsto L l atTop) (hu : ∀ᶠ x in l, 0 ≤ u x)
    (hC : 0 ≤ C) (hp : 0 < p)
    (hbound : ∀ᶠ x in l, u x ≤ C * L x ^ p) :
    Tendsto (fun x => Real.log (u x + 1) / L x) l (𝓝 0) := by
  have hLpos : ∀ᶠ x in l, 0 < L x := hL.eventually_gt_atTop 0
  have hLpow : Tendsto (fun x => L x ^ p) l atTop :=
    (_root_.tendsto_rpow_atTop hp).comp hL
  have hLpowLarge : ∀ᶠ x in l, 1 ≤ L x ^ p :=
    hLpow.eventually_ge_atTop 1
  have hconstant : Tendsto (fun _ : I => Real.log (C + 1)) l
      (𝓝 (Real.log (C + 1))) := tendsto_const_nhds
  have hconstantDiv : Tendsto (fun x => Real.log (C + 1) / L x) l (𝓝 0) := by
    simpa using hconstant.div_atTop hL
  have hlogLDiv : Tendsto (fun x => Real.log (L x) / L x) l (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1
      (by norm_num : (1 : ℝ) ≠ 0)).comp hL
    convert h using 1
    ext x
    simp [pow_one]
  have hupperTendsto : Tendsto
      (fun x => Real.log (C + 1) / L x + p * (Real.log (L x) / L x))
      l (𝓝 0) := by
    simpa using hconstantDiv.add (hlogLDiv.const_mul p)
  have hlower : ∀ᶠ x in l, 0 ≤ Real.log (u x + 1) / L x := by
    filter_upwards [hu, hLpos] with x hux hLx
    apply div_nonneg _ hLx.le
    exact Real.log_nonneg (by linarith)
  have hupper : ∀ᶠ x in l,
      Real.log (u x + 1) / L x ≤
        Real.log (C + 1) / L x + p * (Real.log (L x) / L x) := by
    filter_upwards [hu, hbound, hLpowLarge, hLpos] with x hux hboundx hLpx hLx
    have hLpPos : 0 < L x ^ p := Real.rpow_pos_of_pos hLx p
    have huPlus : 0 < u x + 1 := by linarith
    have hCPlus : 0 < C + 1 := by linarith
    have hboundPlus : u x + 1 ≤ (C + 1) * L x ^ p := by
      calc
        u x + 1 ≤ C * L x ^ p + 1 := by linarith
        _ ≤ C * L x ^ p + L x ^ p := by linarith
        _ = (C + 1) * L x ^ p := by ring
    have hlogBound : Real.log (u x + 1) ≤
        Real.log (C + 1) + p * Real.log (L x) := by
      calc
        Real.log (u x + 1) ≤ Real.log ((C + 1) * L x ^ p) :=
          Real.log_le_log huPlus hboundPlus
        _ = Real.log (C + 1) + p * Real.log (L x) := by
          rw [Real.log_mul (ne_of_gt hCPlus) (ne_of_gt hLpPos), Real.log_rpow hLx]
    have hdiv := div_le_div_of_nonneg_right hlogBound hLx.le
    have heq : (Real.log (C + 1) + p * Real.log (L x)) / L x =
        Real.log (C + 1) / L x + p * (Real.log (L x) / L x) := by
      field_simp [ne_of_gt hLx]
    rw [heq] at hdiv
    exact hdiv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    hupperTendsto hlower hupper

end Asymptotics

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Logarithmic trigonometric asymptotics

* `Real.tendsto_log_cos_div_sq` states
  $\log(\cos x)/x^2\to-1/2$ as $x\to0$ through nonzero values. -/

open Filter
open scoped Topology

@[expose] public section

namespace Real

/-- The local logarithmic asymptotic of cosine. -/
theorem tendsto_log_cos_div_sq :
    Tendsto (fun x : ℝ => Real.log (Real.cos x) / x ^ 2)
      (𝓝[≠] 0) (𝓝 (-1 / 2 : ℝ)) := by
  apply HasDerivAt.lhopital_zero_nhdsNE
      (f' := fun x => -Real.tan x) (g' := fun x => 2 * x)
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (Real.continuous_cos.continuousAt.eventually_ne (by norm_num : Real.cos 0 ≠ 0))] with x hx
    convert (Real.hasDerivAt_cos x).log hx using 1
    rw [Real.tan_eq_sin_div_cos, neg_div]
  · exact Eventually.of_forall fun x => by simpa using (hasDerivAt_pow 2 x)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  · have hc : Tendsto Real.cos (𝓝 (0 : ℝ)) (𝓝 1) := by
      simpa using Real.continuous_cos.tendsto 0
    have hl : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
      simpa using (Real.continuousAt_log one_ne_zero).tendsto
    exact tendsto_nhdsWithin_of_tendsto_nhds (hl.comp hc)
  · exact tendsto_nhdsWithin_of_tendsto_nhds <| by
      simpa using (continuous_pow 2).tendsto (0 : ℝ)
  · have h := Real.tendsto_tan_div_nhdsNE_zero.const_mul (-1 / 2 : ℝ)
    convert h using 1
    · funext x
      field_simp
    · norm_num

end Real

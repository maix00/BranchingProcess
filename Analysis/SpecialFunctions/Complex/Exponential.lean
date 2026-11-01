/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# First-order asymptotics of the complex exponential

For every `z : ℂ`, the real-parameter difference quotient converges to `z`:

\[
\lim_{\substack{t\to 0\\t\ne 0}}
\frac{e^{tz}-1}{t}=z,
\qquad t\in\mathbb{R},\ z\in\mathbb{C}.
\]

## Public declarations

`Complex.tendsto_exp_mul_real_div` gives the slope limit of the exponential along
real parameters: for `z : ℂ`, `(exp(tz) - 1) / t` tends to `z` as real `t` tends
to zero through nonzero values.
-/

public section

open Complex Filter Topology

namespace Complex

/-- The first-order expansion of the complex exponential along a real parameter:
`(exp(tz) - 1) / t → z` as `t → 0` through nonzero values. -/
theorem tendsto_exp_mul_real_div (z : ℂ) :
    Tendsto (fun t : ℝ => (exp ((↑t : ℂ) * z) - 1) / (↑t : ℂ))
      (𝓝[≠] (0 : ℝ)) (𝓝 z) := by
  have hg : HasDerivAt (fun t : ℝ => cexp ((↑t : ℂ) * z)) z 0 := by
    have hf : HasDerivAt (fun t : ℝ => (↑t : ℂ) * z) (1 * z) 0 :=
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const z
    have hexp := hf.cexp
    simp only [ofReal_zero, zero_mul, exp_zero, one_mul, one_mul] at hexp
    exact hexp
  have hslope := hg.tendsto_slope_zero
  simp only [zero_add, ofReal_zero, zero_mul, exp_zero] at hslope
  exact hslope.congr (fun t => by
    show t⁻¹ • (cexp ((↑t : ℂ) * z) - 1) = (cexp ((↑t : ℂ) * z) - 1) / (↑t : ℂ)
    rw [RCLike.real_smul_eq_coe_mul (K := ℂ)]
    push_cast
    rw [inv_mul_eq_div]
    norm_cast)

end Complex

end

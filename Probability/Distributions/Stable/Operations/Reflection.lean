/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Basic
import Probability.Distributions.Stable.Operations.Scaling

/-!
# Reflection of stable laws

## Public declarations

If $\mu$ is $\alpha$-stable, then its reflected law
$\mu\circ(-\mathrm{id})^{-1}$ is $\alpha$-stable; the same statement holds
for strict $\alpha$-stability.

* `IsAlphaStable.map_neg`: reflection preserves α-stability.
* `IsStrictlyAlphaStable.map_neg`: reflection preserves strict α-stability.

Both results specialize `map_mul` to the nonzero scale `-1`.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

/-- Reflection preserves stability as the nonzero scaling `x ↦ -x`. -/
theorem IsAlphaStable.map_neg
    {α : ℝ} {μ : Measure ℝ} (h : IsAlphaStable α μ) :
    IsAlphaStable α (μ.map Neg.neg) := by
  simpa [neg_one_mul] using (h.map_mul (-1) (by norm_num))

/-- Reflection preserves strict stability as the nonzero scaling `x ↦ -x`. -/
theorem IsStrictlyAlphaStable.map_neg
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ) :
    IsStrictlyAlphaStable α (μ.map Neg.neg) := by
  simpa [neg_one_mul] using (h.map_mul (-1) (by norm_num))

end ProbabilityTheory

end

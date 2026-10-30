/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Measure.ExponentialWeight

/-!
# Finite cross-weight assumption

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.HasFiniteCrossWeight`: the condition
  \(\int C_{\varphi,-1}(\xi)\,\mu(d\xi)<\infty\), where
  `Combinatorics.Branching.crossPotentialWeight φ (-1) ξ` is the ordered
  off-diagonal pair sum of the one-child exponential weights.

This predicate is a condition on the raw offspring law. The deterministic
observable and its measurability theorem are owned by
`Combinatorics/BranchingWalk/Step/Measure/ExponentialWeight.lean`.
-/

open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory Combinatorics.Branching

/-- The raw law has finite cross-child exponential weight. -/
def HasFiniteCrossWeight {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X)) : Prop :=
  (∫⁻ ξ, Combinatorics.Branching.crossPotentialWeight φ (-1) ξ ∂μ) ≠ ∞

end ProbabilityTheory.BranchingRandomWalk

end

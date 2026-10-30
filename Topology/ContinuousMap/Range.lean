/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Closed pointwise constraints on continuous maps

## Public declarations

- `ContinuousMap.isClosed_setOf_forall_mem`: for a closed set $F$ in a
  topological space $Y$, the continuous maps $f : X \to Y$ satisfying
  $f(x) \in F$ at every $x$ form a closed subset of $C(X,Y)$.
-/

@[expose] public section

namespace ContinuousMap

/-- Continuous maps whose values all lie in a closed set form a closed
subset of the continuous-map space. -/
theorem isClosed_setOf_forall_mem {X Y : Type*}
    [TopologicalSpace X] [CompactSpace X] [PseudoMetricSpace Y] {F : Set Y}
    (hF : IsClosed F) :
    IsClosed {f : C(X, Y) | ∀ x, f x ∈ F} := by
  rw [show {f : C(X, Y) | ∀ x, f x ∈ F} =
      ⋂ x : X, {f | f x ∈ F} by
    ext f
    simp]
  exact isClosed_iInter fun x => hF.preimage (continuous_eval_const x)

end ContinuousMap

end

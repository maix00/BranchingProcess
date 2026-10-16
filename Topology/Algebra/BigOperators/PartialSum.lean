/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.PartialSum
public import Mathlib.Topology.Algebra.Monoid

/-!
# Continuity of finite partial sums

The finite partial-sum map is continuous when addition in its codomain is
continuous. This is useful whenever a finite vector of increments is sent to
its vector of cumulative positions.
-/

@[expose] public section

namespace Fin

variable {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [ContinuousAdd E]

/-- Taking all finite partial sums is a continuous map on a finite vector. -/
@[continuity, fun_prop]
theorem continuous_partialSum (blocks : ℕ) :
    Continuous (partialSum : (Fin blocks → E) → Fin (blocks + 1) → E) := by
  rw [continuous_pi_iff]
  intro j
  induction j using Fin.induction with
  | zero => exact continuous_const
  | succ j ih =>
    have hc := ih.add (continuous_apply j)
    have heq : (fun x : Fin blocks → E => partialSum x j.succ) =
        (fun x : Fin blocks → E => partialSum x j.castSucc) +
          (fun x : Fin blocks → E => x j) := by
      funext x
      simp only [partialSum_succ, Pi.add_apply]
    exact heq ▸ hc

end Fin

end

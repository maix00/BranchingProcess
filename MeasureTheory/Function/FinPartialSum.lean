/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.PartialSum
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Measurability of finite partial-sum maps

For a measurable additive monoid, each coordinate of the map sending a finite
increment vector to its partial-sum path is measurable. This is the measurable
counterpart of `Fin.continuous_partialSum` and requires no topology on the
state space.
-/

@[expose] public section

namespace Fin

variable {E : Type*} [MeasurableSpace E] [AddMonoid E] [MeasurableAdd₂ E]

/-- The partial sum at a fixed time is measurable as a function of the finite
increment vector. -/
theorem measurable_partialSum {length : ℕ} (time : Fin (length + 1)) :
    Measurable (fun increments : Fin length → E => partialSum increments time) := by
  induction time using Fin.induction with
  | zero => exact measurable_const
  | succ time ih =>
    have hm := ih.add (measurable_pi_apply time)
    have heq : (fun increments : Fin length → E =>
        partialSum increments time.succ) =
      (fun increments : Fin length → E => partialSum increments time.castSucc) +
        (fun increments : Fin length → E => increments time) := by
      funext increments
      simp only [partialSum_succ, Pi.add_apply]
    exact heq ▸ hm

end Fin

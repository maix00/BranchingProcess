/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Tactic.Linarith

/-!
# Limits from eventual error bounds

This file contains sequence-limit assembly lemmas that only use order and
topology.  They are independent of a particular probability application.
-/

@[expose] public section

open Filter Topology

/-- An eventual lower bound within every positive error, together with a
limsup upper bound, determines the limit of a real-valued function. -/
theorem tendsto_of_eventually_sub_pos_le_of_limsup_le
    {ι : Type*} {l : Filter ι} {f : ι → ℝ} {a : ℝ}
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, a - ε ≤ f i)
    (hupper : Filter.limsup f l ≤ a)
    (hbounded : Filter.IsBoundedUnder (· ≤ ·) l f) :
    Tendsto f l (𝓝 a) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro y hy
    let ε : ℝ := (a - y) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    filter_upwards [hlower ε hε] with i hi
    have hy' : y < a - ε := by dsimp [ε]; linarith
    exact hy'.trans_le hi
  · intro y hy
    have hstrict : Filter.limsup f l < y := lt_of_le_of_lt hupper hy
    exact Filter.eventually_lt_of_limsup_lt hstrict hbounded

end

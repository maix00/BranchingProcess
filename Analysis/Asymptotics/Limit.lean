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

/-- If every fixed approximant eventually bounds a function from below and
above, and the corresponding limits converge to the same value as the
approximation index tends to infinity, then the bounded function has that
limit. -/
theorem tendsto_of_eventually_sandwiched_by_convergent_approximants
    {I : Type*} {l : Filter I} [NeBot l]
    (f : I → ℝ) (lower upper : ℕ → I → ℝ)
    (lowerLimit upperLimit : ℕ → ℝ) (L : ℝ)
    (hlower : ∀ n, lower n ≤ᶠ[l] f)
    (hupper : ∀ n, f ≤ᶠ[l] upper n)
    (hlowerRate : ∀ n, Tendsto (lower n) l (𝓝 (lowerLimit n)))
    (hupperRate : ∀ n, Tendsto (upper n) l (𝓝 (upperLimit n)))
    (hlowerLimit : Tendsto lowerLimit atTop (𝓝 L))
    (hupperLimit : Tendsto upperLimit atTop (𝓝 L)) :
    Tendsto f l (𝓝 L) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 <|
      hlowerLimit.eventually (Ioi_mem_nhds hy)
    have hrate := (hlowerRate N).eventually (Ioi_mem_nhds (hN N le_rfl))
    filter_upwards [hlower N, hrate] with x hbound hrate
    exact lt_of_lt_of_le hrate hbound
  · intro y hy
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 <|
      hupperLimit.eventually (Iio_mem_nhds hy)
    have hrate := (hupperRate N).eventually (Iio_mem_nhds (hN N le_rfl))
    filter_upwards [hupper N, hrate] with x hbound hrate
    exact lt_of_le_of_lt hbound hrate

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

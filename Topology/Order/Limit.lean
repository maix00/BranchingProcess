/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Limits from convergent order bounds

This file collects an order-topological limit argument with a second,
approximating index. It is independent of probability and asymptotic-rate
semantics.
-/

@[expose] public section

open Filter Topology

/-- If each fixed approximant eventually bounds a function from below and
above, and the corresponding limits converge to the same value as the
approximation index tends to infinity, then the bounded function has that
limit. -/
theorem tendsto_of_eventually_sandwiched_by_convergent_approximants
    {α I : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {l : Filter I} [NeBot l]
    (f : I → α) (lower upper : ℕ → I → α)
    (lowerLimit upperLimit : ℕ → α) (L : α)
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

end

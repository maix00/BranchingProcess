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

## Public declarations

* `tendsto_of_eventually_sandwiched_by_convergent_approximants`: if for each
  fixed `n` we eventually have `lower n ≤ f ≤ upper n`, and both bounds
  converge along `l` to limits which themselves converge to `L` as `n → ∞`,
  then `f` converges to `L` along `l`. Its hypotheses are
  `∀ n, lower n ≤ᶠ[l] f`, `∀ n, f ≤ᶠ[l] upper n`,
  `Tendsto (lower n) l (𝓝 (lowerLimit n))`,
  `Tendsto (upper n) l (𝓝 (upperLimit n))`, and convergence of both
  `lowerLimit` and `upperLimit` along `atTop` to `L`; the conclusion is
  `Tendsto f l (𝓝 L)`.

The order-topological squeeze statement is
\[
  \left(\forall n,\ \ell_n\le_l f\le_l u_n\right),\quad
  \ell_n\xrightarrow[l]{}a_n,\quad
  u_n\xrightarrow[l]{}b_n,\quad
  a_n,b_n\xrightarrow[n\to\infty]{}L
  \quad\Longrightarrow\quad f\xrightarrow[l]{}L,
\]
where `\ell_n ≤_l f` and `f ≤_l u_n` mean eventual pointwise order along `l`.
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

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Joint logarithmic margins for the weak-tail endpoint estimate

## Internal proof declarations

* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.exists_weakTail_logarithmicParameters`:
  if `0<A<1`, `κ>0` and `ζ>-A+κT`, choose internal tube centers and
  `w,α,ρ,β>0`, `0<dUpper<κ<dLower` so that the one-root success cost is
  below `βw<A`, the finite-root capacity exponent is below `1`, and the
  terminal coefficient is below `ζ`.

This is the numerical assembly for the finite-variance weak-tail extension
of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), Chapter 4, Theorem 1.1, using the cutoff
moments of B. Mallein, *N-branching random walk with α-stable spine*, Lemma 3.4,
arXiv:1503.03762v2. The construction uses `w=1-2ε`, lower offset `A-ε`,
and errors of order `ε²`, leaving strictly positive root and capacity margins.
-/

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
open Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

lemma exists_weakTail_logarithmicParameters {A κ T ζ : ℝ}
    (hA : 0 < A) (hA1 : A < 1) (hκ : 0 < κ)
    (hζ : -A + κ * T < ζ) :
    ∃ w α a b ρ dUpper dLower β : ℝ,
      0 < w ∧ 0 < α ∧ 0 < ρ ∧ 0 < β ∧
      -(1 / 2 : ℝ) < a ∧ a < 1 / 2 ∧ -(1 / 2 : ℝ) < b ∧ b < 1 / 2 ∧
      0 < dUpper ∧ dUpper < κ ∧ κ < dLower ∧ dUpper ≤ κ ∧
      α + 4 * ρ + a + 1 / 2 + 2 * (dLower - dUpper) * (T / w ^ 3) < β ∧
      β * w < A ∧
      A + (1 / 2 - a) * w + max (κ - dUpper) 0 * T / w ^ 2 < 1 ∧
      (b + ρ - a) * w + κ * T / w ^ 2 < ζ := by
  have hid : Tendsto (fun e : ℝ => e) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hroot : Tendsto (fun e : ℝ => e * (5 * (1 - 2 * e) + 4 * T / (1 - 2 * e) ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    have h : ContinuousAt (fun e : ℝ => e * (5 * (1 - 2 * e) + 4 * T / (1 - 2 * e) ^ 2)) 0 := by
      fun_prop (disch := norm_num)
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hcap : Tendsto (fun e : ℝ => e * T / (1 - 2 * e) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h : ContinuousAt (fun e : ℝ => e * T / (1 - 2 * e) ^ 2) 0 := by fun_prop (disch := norm_num)
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hend : Tendsto (fun e : ℝ => -A + e + 2 * e ^ 2 * (1 - 2 * e) +
      κ * T / (1 - 2 * e) ^ 2) (𝓝[>] 0) (𝓝 (-A + κ * T)) := by
    have h : ContinuousAt (fun e : ℝ => -A + e + 2 * e ^ 2 * (1 - 2 * e) +
      κ * T / (1 - 2 * e) ^ 2) 0 := by fun_prop (disch := norm_num)
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  suffices ∀ᶠ e : ℝ in 𝓝[>] 0, ∃ w α a b ρ dUpper dLower β : ℝ,
      0 < w ∧ 0 < α ∧ 0 < ρ ∧ 0 < β ∧
      -(1 / 2 : ℝ) < a ∧ a < 1 / 2 ∧ -(1 / 2 : ℝ) < b ∧ b < 1 / 2 ∧
      0 < dUpper ∧ dUpper < κ ∧ κ < dLower ∧ dUpper ≤ κ ∧
      α + 4 * ρ + a + 1 / 2 + 2 * (dLower - dUpper) * (T / w ^ 3) < β ∧
      β * w < A ∧
      A + (1 / 2 - a) * w + max (κ - dUpper) 0 * T / w ^ 2 < 1 ∧
      (b + ρ - a) * w + κ * T / w ^ 2 < ζ by
    obtain ⟨_, h⟩ := this.exists
    exact h
  filter_upwards [self_mem_nhdsWithin,
    hid.eventually (Iio_mem_nhds hA), hid.eventually (Iio_mem_nhds (sub_pos.mpr hA1)),
    hid.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    (hid.pow 2).eventually (Iio_mem_nhds (by simpa using hκ)),
    hroot.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hcap.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hend.eventually (Iio_mem_nhds hζ)]
    with e he heA heA1 hehalf heκ heroot hecap heend
  have hepos : 0 < e := he
  let w := 1 - 2 * e
  have hw : 0 < w := by dsimp [w]; linarith
  have he2 : 0 < e ^ 2 := sq_pos_of_pos hepos
  let a := (A - e) / w - 1 / 2
  let b := -(1 / 2 : ℝ) + e ^ 2
  let β := (A - e / 2) / w
  refine ⟨w, e ^ 2, a, b, e ^ 2, κ - e ^ 2, κ + e ^ 2, β,
    hw, he2, he2, div_pos (by linarith) hw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [a]
    linarith [div_pos (sub_pos.mpr heA) hw]
  · have h : (A - e) / w < 1 := (div_lt_iff₀ hw).2 (by dsimp [w]; linarith)
    dsimp [a]
    linarith
  · dsimp [b]; linarith
  · dsimp [b]; nlinarith
  · linarith
  · linarith
  · linarith
  · linarith
  · apply (lt_div_iff₀ hw).2
    have h := mul_lt_mul_of_pos_left heroot hepos
    change e * (5 * w + 4 * T / w ^ 2) < 1 / 2 at heroot
    have heq : (e ^ 2 + 4 * e ^ 2 + a + 1 / 2 +
        2 * ((κ + e ^ 2) - (κ - e ^ 2)) * (T / w ^ 3)) * w =
        A - e + e * (e * (5 * w + 4 * T / w ^ 2)) := by
      dsimp [a]
      field_simp [hw.ne']
      ring
    rw [heq]
    change e * (e * (5 * w + 4 * T / w ^ 2)) < e * (1 / 2) at h
    linarith
  · dsimp [β]
    rw [div_mul_cancel₀ _ hw.ne']
    linarith
  · have h := mul_lt_mul_of_pos_left hecap hepos
    have heq : A + (1 / 2 - a) * w + max (κ - (κ - e ^ 2)) 0 * T / w ^ 2 =
        1 - e + e * (e * T / w ^ 2) := by
      rw [show κ - (κ - e ^ 2) = e ^ 2 by ring, max_eq_left he2.le]
      dsimp [a]
      field_simp [hw.ne']
      dsimp [w]
      ring
    rw [heq]
    change e * (e * T / w ^ 2) < e * (1 / 2) at h
    linarith
  · convert heend using 1
    change (b + e ^ 2 - a) * w + κ * T / w ^ 2 =
      -A + e + 2 * e ^ 2 * w + κ * T / w ^ 2
    dsimp [a, b]
    field_simp [hw.ne']
    ring

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

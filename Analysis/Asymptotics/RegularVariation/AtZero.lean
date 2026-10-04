/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Analysis.Asymptotics.RegularVariation

/-!
# Regular variation at zero

This file records the ratio-limit definition of regular variation at the
right-hand neighborhood of zero. It is the natural interface for
characteristic-function defects.
-/

open Filter
open scoped Topology

@[expose] public section

namespace Asymptotics

/-- `f` is regularly varying at zero from the right with index `ρ` if it is
eventually positive there and its ratio under every fixed positive scaling
converges to the corresponding power. -/
def IsRegularlyVaryingAtZero (f : ℝ → ℝ) (ρ : ℝ) : Prop :=
  (∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), 0 < f u) ∧
    ∀ c : ℝ, 0 < c →
      Tendsto (fun u : ℝ => f (c * u) / f u)
        (𝓝[>] (0 : ℝ)) (nhds (c ^ ρ))

namespace IsRegularlyVaryingAtZero

theorem eventually_pos {f : ℝ → ℝ} {ρ : ℝ}
    (h : IsRegularlyVaryingAtZero f ρ) :
    ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), 0 < f u := h.1

theorem ratio_tendsto {f : ℝ → ℝ} {ρ c : ℝ}
    (h : IsRegularlyVaryingAtZero f ρ) (hc : 0 < c) :
    Tendsto (fun u : ℝ => f (c * u) / f u)
      (𝓝[>] (0 : ℝ)) (nhds (c ^ ρ)) := h.2 c hc

/-- Reciprocating the argument converts regular variation at zero into
regular variation at infinity, with the sign of the index reversed. -/
theorem comp_inv {f : ℝ → ℝ} {ρ : ℝ}
    (h : IsRegularlyVaryingAtZero f ρ) :
    IsRegularlyVaryingAtTop (fun x : ℝ => f x⁻¹) (-ρ) := by
  refine ⟨?_, ?_⟩
  · exact tendsto_inv_atTop_nhdsGT_zero.eventually h.eventually_pos
  · intro c hc
    have hratio := (h.ratio_tendsto (inv_pos.mpr hc)).comp
      tendsto_inv_atTop_nhdsGT_zero
    have hratio' : Tendsto (fun x : ℝ =>
        f (c⁻¹ * x⁻¹) / f x⁻¹) atTop (nhds (c⁻¹ ^ ρ)) := by
      convert hratio using 1
      ext x
      rfl
    have hpow : c⁻¹ ^ ρ = c ^ (-ρ) := by
      rw [Real.inv_rpow hc.le, Real.rpow_neg hc.le]
    rw [hpow] at hratio'
    have heq : (fun x : ℝ => f (c⁻¹ * x⁻¹) / f x⁻¹) =ᶠ[atTop]
        fun x => f (c * x)⁻¹ / f x⁻¹ := by
      filter_upwards [] with x
      congr 1
      rw [mul_inv_rev]
      ring_nf
    exact hratio'.congr' heq

end IsRegularlyVaryingAtZero

end Asymptotics

end

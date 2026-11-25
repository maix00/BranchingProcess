/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Lower powers relative to a power normalization

## Public declarations

* `Asymptotics.tendsto_rpow_div_of_ratio_limit`: along any filter, if
  `L→+∞`, `H/L^q→t≠0`, and `p<q`, then `L^p/H→0`.
  Exponents are arbitrary real numbers; `H` need not be positive.

This uses Mathlib's negative-power limit and quotient-limit theorem.
It has no probability, integer-horizon or cubic-scale hypothesis.
-/

@[expose] public section
namespace Asymptotics
open Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

/-- A normalization comparable to a higher power dominates every lower
power. Only the nonzero ratio limit is required. -/
theorem tendsto_rpow_div_of_ratio_limit {I : Type*} {l : Filter I}
    {L H : I → ℝ} {p q t : ℝ}
    (hL : Tendsto L l atTop)
    (hH : Tendsto (fun i => H i / L i ^ q) l (𝓝 t))
    (ht : t ≠ 0) (hpq : p < q) :
    Tendsto (fun i => L i ^ p / H i) l (𝓝 0) := by
  have hpower := (tendsto_rpow_neg_atTop (sub_pos.mpr hpq)).comp hL
  have h := hpower.div hH ht
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [hL.eventually_gt_atTop 0] with i hi
  change L i ^ (-(q - p)) / (H i / L i ^ q) = L i ^ p / H i
  by_cases hHi : H i = 0
  · simp [hHi]
  · rw [show -(q - p) = p - q by ring, Real.rpow_sub hi]
    field_simp [(Real.rpow_pos_of_pos hi q).ne', hHi]

end Asymptotics

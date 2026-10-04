/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Positive error tolerances

This file contains a deterministic topological selection lemma for real-valued
error terms represented in `ENNReal`.  It does not depend on a probability law
or on the random-walk constructions that use it.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace Asymptotics

/-- A quadratic `ENNReal.ofReal` error can be made smaller than any fixed
positive threshold while retaining an arbitrary positive upper bound on its
real parameter. -/
theorem exists_pos_lt_ofReal_mul_sq_div_lt
    {coefficient denominator : ℝ} {probability : ENNReal}
    (hprobability : 0 < probability) {upper : ℝ} (hupper : 0 < upper) :
    ∃ radius : ℝ, 0 < radius ∧ radius < upper ∧
      ENNReal.ofReal (coefficient * (radius ^ 2 / denominator ^ 2)) <
        probability := by
  have hreal : Tendsto
      (fun radius : ℝ => coefficient * (radius ^ 2 / denominator ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hfull : Tendsto
        (fun radius : ℝ => coefficient * (radius ^ 2 / denominator ^ 2))
        (𝓝 0) (𝓝 0) := by
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => coefficient)
          (𝓝 0) (𝓝 coefficient)).mul
          (((tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).pow 2).div_const
            (denominator ^ 2))
    exact hfull.mono_left inf_le_left
  have hennreal : Tendsto
      (fun radius : ℝ =>
        ENNReal.ofReal (coefficient * (radius ^ 2 / denominator ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  have hsmall : ∀ᶠ radius in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (coefficient * (radius ^ 2 / denominator ^ 2)) <
        probability :=
    (tendsto_order.1 hennreal).2 _ hprobability
  have hinterval : ∀ᶠ radius in 𝓝[>] (0 : ℝ),
      radius ∈ Ioo 0 upper := Ioo_mem_nhdsGT hupper
  obtain ⟨radius, hradius, herror⟩ := (hinterval.and hsmall).exists
  exact ⟨radius, hradius.1, hradius.2, herror⟩

end Asymptotics

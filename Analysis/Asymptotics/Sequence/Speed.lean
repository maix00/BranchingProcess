/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Asymptotic speed of a sequence

## Public declarations

* `HasAsymptoticSpeed p c` means that $(n : \mathbb K)^{-1} \cdot p_n$
  converges to $c$.
* `hasAsymptoticSpeed_unique` gives uniqueness in a Hausdorff space.
* `hasAsymptoticSpeed_iff_nat_add` expresses the same limit after shifting the
  sequence and its denominator by the same fixed index.
-/

open Filter
open scoped Topology

@[expose] public section

namespace Asymptotics

variable {𝕜 X : Type*} [Field 𝕜] [TopologicalSpace X] [SMul 𝕜 X]

/-- A sequence of positions has asymptotic speed `c` when `p n / n` converges
to `c`. -/
def HasAsymptoticSpeed (p : ℕ → X) (c : X) : Prop :=
  Tendsto (fun n : ℕ => ((n : 𝕜))⁻¹ • p n) atTop (𝓝 c)

/-- The asymptotic speed of a sequence is unique. -/
theorem hasAsymptoticSpeed_unique [T2Space X] {p : ℕ → X} {c d : X}
    (hc : HasAsymptoticSpeed (𝕜 := 𝕜) p c)
    (hd : HasAsymptoticSpeed (𝕜 := 𝕜) p d) :
    c = d :=
  tendsto_nhds_unique hc hd

/-- The normalized trajectory converges to the same speed after deleting any
fixed finite prefix. The denominator remains the absolute generation index
`n + k`, so this form applies directly after a deterministic stopping time. -/
theorem hasAsymptoticSpeed_iff_nat_add (p : ℕ → X) (c : X) (k : ℕ) :
    HasAsymptoticSpeed (𝕜 := 𝕜) p c ↔
      Tendsto
        (fun n : ℕ => (((n + k : ℕ) : 𝕜)⁻¹) • p (n + k))
        atTop (𝓝 c) := by
  constructor
  · intro h
    exact (tendsto_add_atTop_iff_nat
      (f := fun n : ℕ => ((n : 𝕜)⁻¹) • p n) k).2 h
  · intro h
    exact (tendsto_add_atTop_iff_nat
      (f := fun n : ℕ => ((n : 𝕜)⁻¹) • p n) k).1 h

end Asymptotics

end

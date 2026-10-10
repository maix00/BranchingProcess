/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Analytic closure of the speed limit

This file turns eventual two-sided estimates into the limiting speed formula.
-/

open Filter Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

/-- The precise analytic last step of Theorem 1.2.  The two eventual
inequalities may come from different couplings or truncated laws. -/
theorem speed_limit_of_eventual_bounds
    (v : ℕ → ℝ) (σ2 : ℝ)
    (hbound : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N in atTop,
        Real.pi ^ 2 * σ2 / 2 - ε ≤ v N * (Real.log (N : ℝ)) ^ 2 ∧
        v N * (Real.log (N : ℝ)) ^ 2 ≤ Real.pi ^ 2 * σ2 / 2 + ε) :
    Tendsto (fun N : ℕ => v N * (Real.log (N : ℝ)) ^ 2)
      atTop (𝓝 (Real.pi ^ 2 * σ2 / 2)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hε : 0 < (Real.pi ^ 2 * σ2 / 2 - b) / 2 := by linarith
    filter_upwards [hbound _ hε] with N hN
    linarith [hN.1]
  · intro b hb
    have hε : 0 < (b - Real.pi ^ 2 * σ2 / 2) / 2 := by linarith
    filter_upwards [hbound _ hε] with N hN
    linarith [hN.2]

end ProbabilityTheory.BranchingRandomWalk

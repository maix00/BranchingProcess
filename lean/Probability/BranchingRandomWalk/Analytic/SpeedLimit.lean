import Mathlib.Topology.Order.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Analytic closure of the speed limit

This file turns eventual two-sided estimates into the limiting speed formula.
-/

open Filter Topology

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

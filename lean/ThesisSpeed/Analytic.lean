import Mathlib.Topology.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Analytic closure of the speed theorem

The probabilistic estimates in Thesis Theorem 1.2 are **not** assumed here in the
form of the desired conclusion.  The input is an eventual upper and lower bound
for every positive error.  Once those bounds have been established for the
N-branching random walk, this file proves the limiting speed formula.

No `sorry`, axioms, or opaque probability-law assumptions occur in this file.
-/

open Filter Topology

namespace ThesisSpeed

/-- A pointwise truncation inequality.  After integration, this is the
first-moment replacement for a Cauchy--Schwarz estimate on a rare event. -/
theorem bad_event_truncation (x K : ℝ) (event : Prop) [Decidable event] (hK : 0 ≤ K) :
    (if event then |x| else 0) ≤
      (if K < |x| then |x| else 0) + K * (if event then 1 else 0) := by
  classical
  by_cases he : event
  · simp only [if_pos he, mul_one]
    by_cases hx : K < |x|
    · simp only [if_pos hx]
      linarith
    · simp only [if_neg hx]
      simpa using (le_of_not_gt hx)
  · simp only [if_neg he, mul_zero, add_zero]
    split_ifs <;> positivity

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

end ThesisSpeed

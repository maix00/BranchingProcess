import Mathlib.Topology.Order.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Analytic closure of the speed theorem

The probabilistic estimates in Thesis Theorem 1.2 are **not** assumed here in the
form of the desired conclusion.  The input is an eventual upper and lower bound
for every positive error.  Once those bounds have been established for the
N-branching random walk, this file proves the limiting speed formula.

No `sorry`, axioms, or opaque probability-law assumptions occur in this file.
-/

open Filter Topology
open scoped BigOperators

namespace ProbabilityTheory.BranchingRandomWalk


/-- A pointwise truncation inequality.  After integration, this is the
first-moment replacement for a Cauchy--Schwarz estimate on a rare event. -/
theorem bad_event_truncation (x K : ℝ) (event : Prop) [Decidable event] (hK : 0 ≤ K) :
    (if event then |x| else 0) ≤
      (if K < |x| then |x| else 0) + K * (if event then 1 else 0) := by
  classical
  by_cases he : event
  · simp only [ite_eq_left he, mul_one]
    by_cases hx : K < |x|
    · simp only [ite_eq_left hx]
      linarith
    · simp only [ite_eq_right hx]
      simpa using (le_of_not_gt hx)
  · simp only [ite_eq_right he, mul_zero, add_zero]
    split_ifs <;> positivity

/-! The same estimate summed over a finite labelled family.  This is the
finite-population form used before passing to a measure or a lintegral. -/
theorem bad_event_truncation_sum {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (event : ι → Prop) [DecidablePred event]
    (K : ℝ) (hK : 0 ≤ K) :
    s.sum (fun i => if event i then |x i| else 0) ≤
      s.sum (fun i => (if K < |x i| then |x i| else 0) +
        K * (if event i then 1 else 0)) := by
  exact Finset.sum_le_sum fun i hi => bad_event_truncation (x i) K
    (event i) hK

theorem bad_event_truncation_sum_card {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (event : ι → Prop) [DecidablePred event]
    (K : ℝ) (hK : 0 ≤ K) :
    s.sum (fun i => if event i then |x i| else 0) ≤
      s.sum (fun i => if K < |x i| then |x i| else 0) +
        K * (s.filter event).card := by
  calc
    s.sum (fun i => if event i then |x i| else 0) ≤
        s.sum (fun i => (if K < |x i| then |x i| else 0) +
          K * (if event i then 1 else 0)) :=
      bad_event_truncation_sum s x event K hK
    _ = s.sum (fun i => if K < |x i| then |x i| else 0) +
          K * (s.filter event).card := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [← Finset.mul_sum]
      congr 1
      simp [Finset.sum_boole]

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

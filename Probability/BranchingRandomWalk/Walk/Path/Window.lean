import Probability.BranchingRandomWalk.Walk.Path

/-!
# Measurable windows for finite random-walk paths
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

/-- A finite path remains in the prescribed window at every coordinate. -/
def InWindows {n : ℕ} (window : Fin (n + 1) → Set ℝ)
    (path : Fin (n + 1) → ℝ) : Prop :=
  ∀ k, path k ∈ window k

theorem measurableSet_inWindows {n : ℕ}
    (window : Fin (n + 1) → Set ℝ)
    (hwindow : ∀ k, MeasurableSet (window k)) :
    MeasurableSet {path : Fin (n + 1) → ℝ | InWindows window path} := by
  rw [show {path : Fin (n + 1) → ℝ | InWindows window path} =
      ⋂ k, {path | path k ∈ window k} by
    ext path
    simp [InWindows]]
  exact MeasurableSet.iInter fun k =>
    (hwindow k).preimage (measurable_pi_apply k)

/-- Indicator of a finite path-window event. -/
noncomputable def windowTest {n : ℕ}
    (window : Fin (n + 1) → Set ℝ) :
    (Fin (n + 1) → ℝ) → ENNReal :=
  {path | InWindows window path}.indicator fun _ => 1

theorem windowTest_measurable {n : ℕ}
    (window : Fin (n + 1) → Set ℝ)
    (hwindow : ∀ k, MeasurableSet (window k)) :
    Measurable (windowTest window) :=
  measurable_const.indicator (measurableSet_inWindows window hwindow)

@[simp] theorem windowTest_eq_one_iff {n : ℕ}
    (window : Fin (n + 1) → Set ℝ) (path : Fin (n + 1) → ℝ) :
    windowTest window path = 1 ↔ InWindows window path := by
  simp [windowTest]

@[simp] theorem windowTest_eq_zero_iff {n : ℕ}
    (window : Fin (n + 1) → Set ℝ) (path : Fin (n + 1) → ℝ) :
    windowTest window path = 0 ↔ ¬InWindows window path := by
  simp [windowTest]

end ProbabilityTheory.BranchingRandomWalk.RandomWalk

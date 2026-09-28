import Probability.BranchingRandomWalk.Spine.Path.Basic
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.RelativePosition

/-!
# Measurable path-window events

These definitions live on finite real-valued histories and are independent of
any branching realization.  A restarted window compares each path coordinate
with the coordinate selected by a deterministic anchor schedule.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

/-- A finite history remains in the prescribed absolute window at every
coordinate. -/
def InWindows {n : ℕ} (window : Fin (n + 1) → Set ℝ)
    (history : Fin (n + 1) → ℝ) : Prop :=
  ∀ k, history k ∈ window k

theorem measurableSet_inWindows {n : ℕ}
    (window : Fin (n + 1) → Set ℝ)
    (hwindow : ∀ k, MeasurableSet (window k)) :
    MeasurableSet {history : Fin (n + 1) → ℝ | InWindows window history} := by
  rw [show {history : Fin (n + 1) → ℝ | InWindows window history} =
      ⋂ k, {history | history k ∈ window k} by
    ext history
    simp [InWindows]]
  exact MeasurableSet.iInter fun k =>
    (hwindow k).preimage (measurable_pi_apply k)

/-- A finite history remains in moving windows after subtracting the history
at the deterministic restart anchor associated with each time. -/
def InRestartedWindows {n : ℕ} (cutoff : ℕ) (window : ℕ → Set ℝ)
    (history : Fin (n + 1) → ℝ) : Prop :=
  ∀ k : Fin (n + 1), history k - history
    ⟨RootIndexed.restartAnchor cutoff k,
      (RootIndexed.restartAnchor_le cutoff k).trans_lt k.2⟩ ∈ window k

theorem measurableSet_inRestartedWindows {n : ℕ}
    (cutoff : ℕ) (window : ℕ → Set ℝ)
    (hwindow : ∀ k, MeasurableSet (window k)) :
    MeasurableSet {history : Fin (n + 1) → ℝ |
      InRestartedWindows cutoff window history} := by
  rw [show {history : Fin (n + 1) → ℝ |
        InRestartedWindows cutoff window history} =
      ⋂ k : Fin (n + 1), {history | history k - history
        ⟨RootIndexed.restartAnchor cutoff k,
          (RootIndexed.restartAnchor_le cutoff k).trans_lt k.2⟩ ∈ window k} by
    ext history
    simp [InRestartedWindows]]
  apply MeasurableSet.iInter
  intro k
  exact (hwindow k).preimage
    ((measurable_pi_apply k).sub (measurable_pi_apply
      (⟨RootIndexed.restartAnchor cutoff k,
        (RootIndexed.restartAnchor_le cutoff k).trans_lt k.2⟩ :
          Fin (n + 1))))

/-- Indicator of the restarted path-window event, in the codomain used by
path-functional many-to-one identities. -/
noncomputable def restartedWindowTest {n : ℕ} (cutoff : ℕ)
    (window : ℕ → Set ℝ) : (Fin (n + 1) → ℝ) → ENNReal :=
  {history | InRestartedWindows cutoff window history}.indicator fun _ => 1

theorem restartedWindowTest_measurable {n : ℕ} (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k)) :
    Measurable (restartedWindowTest (n := n) cutoff window) :=
  measurable_const.indicator
    (measurableSet_inRestartedWindows cutoff window hwindow)

@[simp] theorem restartedWindowTest_eq_one_iff {n : ℕ} (cutoff : ℕ)
    (window : ℕ → Set ℝ) (history : Fin (n + 1) → ℝ) :
    restartedWindowTest cutoff window history = 1 ↔
      InRestartedWindows cutoff window history := by
  simp [restartedWindowTest]

@[simp] theorem restartedWindowTest_eq_zero_iff {n : ℕ} (cutoff : ℕ)
    (window : ℕ → Set ℝ) (history : Fin (n + 1) → ℝ) :
    restartedWindowTest cutoff window history = 0 ↔
      ¬InRestartedWindows cutoff window history := by
  simp [restartedWindowTest]

end ProbabilityTheory.BranchingRandomWalk.Spine

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Restart.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Measurability of finite restarted-window events

## Public declarations

- `ProbabilityTheory.Process.Path.measurableSet_inRestartedWindows`: if
  subtraction on `E` is measurable and each `window k` is measurable, then
  the event
  `{x : Fin (n + 1) → E | ∀ k, x k - x (restartAnchor cutoff k) ∈ window k}`
  is measurable in the finite-coordinate product space.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Process.Path

/-- A finite path's restarted-window event is measurable when subtraction
and each coordinate window are measurable. -/
theorem measurableSet_inRestartedWindows {E : Type*} [MeasurableSpace E]
    [Sub E] [MeasurableSub₂ E] {n : ℕ} (cutoff : ℕ)
    (window : ℕ → Set E)
    (hwindow : ∀ k, MeasurableSet (window k)) :
    MeasurableSet {path : Fin (n + 1) → E |
      InRestartedWindows cutoff window path} := by
  rw [show {path : Fin (n + 1) → E |
        InRestartedWindows cutoff window path} =
      ⋂ k : Fin (n + 1), {path |
        path k - path
          ⟨restartAnchor cutoff k,
            by have h := restartAnchor_le cutoff k; omega⟩ ∈ window k} by
    ext path
    simp [InRestartedWindows]]
  apply MeasurableSet.iInter
  intro k
  have hanchor : Measurable (fun path : Fin (n + 1) → E =>
      path ⟨restartAnchor cutoff k,
        by have h := restartAnchor_le cutoff k; omega⟩) :=
    measurable_pi_apply _
  have hdifference : Measurable (fun path : Fin (n + 1) → E =>
      path k - path ⟨restartAnchor cutoff k,
        by have h := restartAnchor_le cutoff k; omega⟩) := by
    exact measurable_sub.comp ((measurable_pi_apply k).prodMk hanchor)
  exact (hwindow k).preimage hdifference

end ProbabilityTheory.Process.Path

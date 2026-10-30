/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Restart.Windows
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Probability of restarted walk paths

This file defines the probability of the deterministic restarted-window
event and records invariance under translation of the initial position.

## Public declarations

* `ProbabilityTheory.RandomWalk.restartedWindowProbability` assigns the
  increment law's measure to the event
  `InRestartedWindows cutoff window (history n initial increment)`.
* `ProbabilityTheory.RandomWalk.restartedWindowProbability_eq_zeroInitial`
  states that this probability is independent of `initial`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

open ProbabilityTheory.Process.Path


/-- Probability of a restarted-window event under an increment-path law. -/
def restartedWindowProbability
    (incrementLaw : Measure (ℕ → ℝ)) (cutoff : ℕ)
    (window : ℕ → Set ℝ) (n : ℕ) (initial : ℝ) : ENNReal :=
  incrementLaw {increment | InRestartedWindows cutoff window
    (history n initial increment)}

/-- Restarted-window membership and probability are invariant under
translation of the absolute initial position. -/
theorem restartedWindowProbability_eq_zeroInitial
    (incrementLaw : Measure (ℕ → ℝ)) (cutoff : ℕ)
    (window : ℕ → Set ℝ) (n : ℕ) (initial : ℝ) :
    restartedWindowProbability incrementLaw cutoff window n initial =
      restartedWindowProbability incrementLaw cutoff window n 0 := by
  unfold restartedWindowProbability
  congr 1
  ext increment
  exact inRestartedWindows_history_iff cutoff window initial increment

end ProbabilityTheory.RandomWalk

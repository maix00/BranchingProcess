/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Restart.Windows
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Measure of restarted walk paths

This file defines the increment measure of the deterministic restarted-window
event and records invariance under translation of the initial position.

## Public declarations

For an increment measure $\nu$, define
$\Pi_{\nu,c,W,n}(x)=\nu\{\xi:\operatorname{InRestartedWindows}
(c,W,\operatorname{history}(n,x,\xi))\}$. Translation invariance gives
$\Pi_{\nu,c,W,n}(x)=\Pi_{\nu,c,W,n}(0)$; when $\nu$ is a probability
measure, this quantity is the event probability.

* `ProbabilityTheory.RandomWalk.restartedWindowProbability` assigns the
  increment law's measure to the event
  `InRestartedWindows cutoff window (history n initial increment)`.
* `ProbabilityTheory.RandomWalk.restartedWindowProbability_eq_zeroInitial`
  states that this event measure is independent of `initial`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

open ProbabilityTheory.Process.Path


/-- Measure of a restarted-window event under an increment-path law. -/
def restartedWindowProbability
    (incrementLaw : Measure (ℕ → ℝ)) (cutoff : ℕ)
    (window : ℕ → Set ℝ) (n : ℕ) (initial : ℝ) : ENNReal :=
  incrementLaw {increment | InRestartedWindows cutoff window
    (history n initial increment)}

/-- Restarted-window membership and its event measure are invariant under
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

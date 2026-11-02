/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Restart.Basic
public import Probability.Sequence.IID.Basic
import Probability.Process.RandomWalk.Path.Window.Core
import all Probability.Process.RandomWalk.Path.Restart.Lemmas.IntervalFactorization

/-!
# Restarted interval probabilities

For IID increments, a path constrained to one closed interval before and after
a deterministic restart has the product law of its prefix and shifted tail.

## Public declarations

* `ProbabilityTheory.RandomWalk.restartedWindowProbability_Icc_add_eq_mul`:
  for a constant window $[a,b]$, the probability through `cutoff + tail` is
  the product of the zero-started prefix and tail probabilities.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

open ProbabilityTheory.Process.Path

/-- For a constant closed interval under the canonical IID increment law, a
restarted-window probability is the product of the zero-started prefix and
tail probabilities. -/
theorem restartedWindowProbability_Icc_add_eq_mul
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (lower upper : ℝ) (cutoff tail : ℕ) (initial : ℝ) :
    restartedWindowProbability (iidSequenceLaw ν) cutoff
        (fun _ => Set.Icc lower upper) (cutoff + tail) initial =
      iidSequenceLaw ν {increment |
          InClosedInterval lower upper cutoff 0 increment} *
        iidSequenceLaw ν {increment |
          InClosedInterval lower upper tail 0 increment} := by
  rw [restartedWindowProbability_eq_zeroInitial]
  unfold restartedWindowProbability
  rw [show {increment : ℕ → ℝ |
        InRestartedWindows cutoff (fun _ => Set.Icc lower upper)
          (history (cutoff + tail) 0 increment)} =
      {increment |
        InClosedInterval lower upper cutoff 0 increment ∧
          InClosedInterval lower upper tail 0
            (fun k => increment (cutoff + k))} by
    ext increment
    exact inRestartedWindows_Icc_add_iff
      lower upper cutoff tail 0 increment]
  exact Restart.Lemmas.iidSequenceLaw_closedInterval_prefix_shift_mul
    ν lower upper cutoff tail

end ProbabilityTheory.RandomWalk

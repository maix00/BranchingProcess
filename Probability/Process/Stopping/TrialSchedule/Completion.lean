/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Process.Stopping

/-!
# Fixed-duration completions of scheduled trials

For a family of trial start times $(T_i)_{i\in\mathbb N}$, define the fixed-
duration completion by $C_i=T_i+d$. This construction preserves the stopping-
time property, and a monotone family of start times gives a monotone family of
completion times.
## Public declarations

- `completion start duration i ω = start i ω + duration` is the fixed-duration
  completion of any family of trial start times.
- `completion_isStoppingTime` and `completion_mono` preserve the stopping-time
  and monotonicity properties of the start times.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.Process.Stopping.TrialSchedule

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Completion of trial `i` a fixed number of steps after its scheduled start. -/
noncomputable def completion
    (start : ℕ → Ω → WithTop ℕ) (duration i : ℕ) (ω : Ω) : WithTop ℕ :=
  start i ω + duration

theorem completion_isStoppingTime
    (F : Filtration ℕ m) (start : ℕ → Ω → WithTop ℕ) (i : ℕ)
    (hstart : IsStoppingTime F (start i)) (duration : ℕ) :
    IsStoppingTime F (completion start duration i) :=
  hstart.add_const' duration

theorem completion_mono
    (start : ℕ → Ω → WithTop ℕ)
    (hstart : ∀ ω, Monotone fun i => start i ω)
    (duration : ℕ) (ω : Ω) :
    Monotone fun i => completion start duration i ω := by
  intro i j hij
  simpa [completion] using add_le_add_left
    (hstart ω hij) (duration : WithTop ℕ)

end ProbabilityTheory.Process.Stopping.TrialSchedule

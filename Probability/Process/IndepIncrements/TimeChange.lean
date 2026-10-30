/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic

/-!
# Time changes of processes with independent increments

## Public declarations

* `HasIndepIncrements.comp_time`: for a monotone deterministic map
  `φ : Time' → Time`,
  `HasIndepIncrements X P → HasIndepIncrements (fun t ω => X (φ t) ω) P`.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

variable {Time Time' Ω E : Type*}
  [Preorder Time] [Preorder Time'] [MeasurableSpace Ω] [MeasurableSpace E]
  {P : Measure Ω} {X : Time → Ω → E} [Sub E]

/-- Composing a process with a monotone deterministic time map preserves
independent increments. -/
theorem HasIndepIncrements.comp_time
    (hX : HasIndepIncrements X P) (φ : Time' → Time) (hφ : Monotone φ) :
    HasIndepIncrements (fun t ω => X (φ t) ω) P := by
  intro n t ht
  simpa using hX n (fun i => φ (t i)) (hφ.comp ht)

end ProbabilityTheory

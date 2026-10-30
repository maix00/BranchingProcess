/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.IdentDistrib

/-!
# Processes with stationary increments

## Public declarations

- `ProbabilityTheory.HasStationaryIncrements X P` means that translated
  increments have a common law:
  $\forall s,t,\quad X_{s+t}-X_s\;\stackrel{P}{=}\;X_t-X_0$.
  The definition uses an additive time monoid and subtraction on the state
  space.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A process has stationary increments when the law of the increment over
an interval depends only on the interval's duration. -/
def HasStationaryIncrements {Time E : Type*} [AddMonoid Time]
    [MeasurableSpace E] [Sub E]
    (X : Time → Ω → E) (P : Measure Ω) : Prop :=
  ∀ s t : Time,
    IdentDistrib (fun ω => X (s + t) ω - X s ω)
      (fun ω => X t ω - X 0 ω) P P

end ProbabilityTheory

end

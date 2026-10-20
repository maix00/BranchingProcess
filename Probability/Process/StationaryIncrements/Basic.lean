/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.IdentDistrib

/-!
# Processes with stationary increments

The public definition `HasStationaryIncrements X P` is
`$X_{s+t}-X_s \stackrel{d}{=} X_t-X_0$` for every `s` and `t`. It assumes
only an additive time monoid and subtraction on the state space; independent
increments and path regularity are separate properties.
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

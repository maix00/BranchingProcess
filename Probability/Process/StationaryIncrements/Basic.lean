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
- `ProbabilityTheory.HasStationaryIncrements.identDistrib_increment_of_ae_start`:
  if $X_0=0$ almost surely, then the increment over an interval of length $t$
  has the same law as $X_t$:
  $X_{s+t}-X_s\;\stackrel{P}{=}\;X_t$.
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

namespace HasStationaryIncrements

variable {Time E : Type*} [AddMonoid Time]
  [MeasurableSpace E] [SubNegZeroMonoid E]
variable {X : Time → Ω → E} {P : Measure Ω}

/-- For a stationary-increment process that starts at zero almost surely,
the law of the increment over an interval of duration `t` is the law of the
position at time `t`. -/
theorem identDistrib_increment_of_ae_start
    (h : HasStationaryIncrements X P)
    (hstart : ∀ᵐ ω ∂P, X 0 ω = 0) (s t : Time) :
    IdentDistrib (fun ω => X (s + t) ω - X s ω)
      (fun ω => X t ω) P P := by
  have hstationary := h s t
  have hzero : (fun ω => X t ω - X 0 ω) =ᵐ[P]
      fun ω => X t ω := by
    filter_upwards [hstart] with ω hω
    simp [hω]
  exact hstationary.trans
    (IdentDistrib.of_ae_eq hstationary.aemeasurable_snd hzero)

end HasStationaryIncrements

end ProbabilityTheory

end

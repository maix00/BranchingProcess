/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Levy.Basic
public import Probability.Process.IndepIncrements.FiniteDimensional

/-!
# Finite-dimensional measurability of Lévy processes

## Public declarations

- `ProbabilityTheory.IsLevyProcess.aemeasurable_eval` proves that every
  coordinate map of a real-valued Lévy process is almost-everywhere
  measurable. Stationarity makes each increment measurable from its law,
  and the zero initial value then gives measurability of the coordinates.

The general independent-increment measurability argument is in
`Probability.Process.IndepIncrements.FiniteDimensional`; this file applies it
to stationary Lévy increments.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory.IsLevyProcess

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {X : ℝ≥0 → Ω → ℝ}

/-- Every coordinate of a real-valued Lévy process is almost-everywhere
measurable. Stationary increments give measurable increments through their
identical distributions, and the starting value is zero almost surely. -/
theorem aemeasurable_eval (h : IsLevyProcess X P) (t : ℝ≥0) :
    AEMeasurable (fun ω => X t ω) P := by
  apply HasIndepIncrements.aemeasurable_eval h.ae_start_eq_zero
  intro s t hst
  let d := t - s
  have hsum : s + d = t := add_tsub_cancel_of_le hst
  have hstationary := h.stationaryIncrements s d
  have heq : (fun ω => X (s + d) ω - X s ω) =ᵐ[P]
      fun ω => X t ω - X s ω := by
    filter_upwards with ω
    rw [hsum]
  exact hstationary.aemeasurable_fst.congr heq

end ProbabilityTheory.IsLevyProcess

end

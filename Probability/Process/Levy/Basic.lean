/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Probability.Process.StationaryIncrements.Basic
public import Topology.Cadlag.Basic

/-!
# Lévy processes

## Public declarations

- `ProbabilityTheory.IsLevyProcess`: a real-time process $X$ starts at zero
  almost surely, has independent and stationary increments, and has càdlàg
  paths almost surely.
- `ProbabilityTheory.IsLevyProcess.ae_start_eq_zero`:
  $X_0=0$ almost surely.
- `ProbabilityTheory.IsLevyProcess.indepIncrements`:
  $X$ has independent increments.
- `ProbabilityTheory.IsLevyProcess.stationaryIncrements`:
  increments over intervals of equal length have the same law.
- `ProbabilityTheory.IsLevyProcess.ae_cadlag`:
  sample paths of $X$ are càdlàg almost surely.

Stable increment laws are specialized in `Probability.Process.Stable`.
-/

open MeasureTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A real-time Lévy process with values in a topological additive group:
it starts at zero, has stationary independent increments, and has almost
surely càdlàg paths. -/
def IsLevyProcess {E : Type*} [AddGroup E] [MeasurableSpace E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [BorelSpace E]
    (X : ℝ≥0 → Ω → E) (P : Measure Ω) [IsProbabilityMeasure P] : Prop :=
  (∀ᵐ ω ∂P, X 0 ω = 0) ∧
    HasIndepIncrements X P ∧
    HasStationaryIncrements X P ∧
    (∀ᵐ ω ∂P, IsCadlag (fun t => X t ω))

namespace IsLevyProcess

variable {E : Type*} [AddGroup E] [MeasurableSpace E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [BorelSpace E]
variable {X : ℝ≥0 → Ω → E} {P : Measure Ω} [IsProbabilityMeasure P]

theorem ae_start_eq_zero (h : IsLevyProcess X P) :
    ∀ᵐ ω ∂P, X 0 ω = 0 := h.1

theorem indepIncrements (h : IsLevyProcess X P) :
    HasIndepIncrements X P := h.2.1

theorem stationaryIncrements (h : IsLevyProcess X P) :
    HasStationaryIncrements X P := h.2.2.1

theorem ae_cadlag (h : IsLevyProcess X P) :
    ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω) := h.2.2.2

end IsLevyProcess

end ProbabilityTheory

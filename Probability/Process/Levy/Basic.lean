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

The public definition `IsLevyProcess X P` is the conjunction of: `X 0 = 0`
almost surely, `HasIndepIncrements X P`, `HasStationaryIncrements X P`, and
almost-sure càdlàg paths. Its four projection theorems expose these defining
properties separately. Stable increment laws are a specialization in
`Probability.Process.Stable`.
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

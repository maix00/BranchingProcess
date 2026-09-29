import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Topology.Cadlag.Basic

/-!
# Lévy processes

The process-level interfaces use Mathlib's convention `Time → Ω → State`.
This file defines real-time Lévy processes with an abstract topological
additive-group state space. Stable increment laws are a specialization in
`Probability.Process.Stable`.
-/

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A real-time process has stationary increments when every increment over
an interval of length `t` has the same law as its increment over `[0,t]`. -/
def HasStationaryIncrements {E : Type*} [MeasurableSpace E] [Sub E]
    (X : ℝ≥0 → Ω → E) (P : Measure Ω) : Prop :=
  ∀ s t : ℝ≥0,
    IdentDistrib (fun ω => X (s + t) ω - X s ω)
      (fun ω => X t ω - X 0 ω) P P

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

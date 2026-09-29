module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

@[expose] public section

/-!
# Continuous sample paths

This file turns a process whose every sample path is continuous into a
continuous-map-valued function. Randomness remains in the outer argument:
processes use mathlib's convention `Time → Ω → State`.
-/

namespace ProbabilityTheory

/-- Bundle the sample paths of a process as continuous maps. -/
def continuousPath {Time Ω State : Type*}
    [TopologicalSpace Time] [TopologicalSpace State]
    (X : Time → Ω → State) (hX : ∀ ω, Continuous (fun t ↦ X t ω)) :
    Ω → C(Time, State) :=
  fun ω ↦ ⟨fun t ↦ X t ω, hX ω⟩

@[simp]
theorem continuousPath_apply {Time Ω State : Type*}
    [TopologicalSpace Time] [TopologicalSpace State]
    (X : Time → Ω → State) (hX : ∀ ω, Continuous (fun t ↦ X t ω))
    (t : Time) (ω : Ω) :
    continuousPath X hX ω t = X t ω :=
  rfl

/-- A process with measurable coordinates and continuous sample paths is a
random variable with values in the continuous-path space. -/
theorem measurable_continuousPath {Time Ω State : Type*}
    [TopologicalSpace Time] [SecondCountableTopology Time]
    [LocallyCompactSpace Time] [MeasurableSpace Ω]
    [TopologicalSpace State] [SecondCountableTopology State]
    [RegularSpace State] [MeasurableSpace State] [BorelSpace State]
    (X : Time → Ω → State) (hX : ∀ ω, Continuous (fun t ↦ X t ω))
    (hXmeas : ∀ t, Measurable (X t)) :
    Measurable (continuousPath X hX) := by
  rw [ContinuousMap.measurable_iff_eval]
  simpa using hXmeas

end ProbabilityTheory

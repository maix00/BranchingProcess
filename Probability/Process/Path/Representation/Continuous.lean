/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Continuous sample paths

## Public declarations

- `ProbabilityTheory.continuousPath`: bundles the sample paths of a process
  with continuous paths as an element of $C(\mathrm{Time},\mathrm{State})$.
- `ProbabilityTheory.continuousPath_apply`: evaluation of that bundle
  recovers the original process coordinate.
- `ProbabilityTheory.measurable_continuousPath`: measurable coordinates
  make the continuous-path-valued random variable measurable.
- `ProbabilityTheory.exists_measurable_continuousPathVersion`: measurable
  coordinates and almost-sure continuity give a measurable path-valued
  version agreeing with the process simultaneously at all times almost surely.

Processes use mathlib's convention `Time → Ω → State`.
-/

@[expose] public section

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

/-- A process with measurable coordinates and almost surely continuous paths
has a measurable continuous-path-valued version that agrees with it at every
time on one event of full measure. -/
theorem exists_measurable_continuousPathVersion
    {Time Ω State : Type*} [TopologicalSpace Time]
    [SecondCountableTopology Time] [LocallyCompactSpace Time]
    [TopologicalSpace State] [SecondCountableTopology State] [RegularSpace State]
    [MeasurableSpace State] [BorelSpace State] [Nonempty C(Time, State)]
    [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : Time → Ω → State)
    (hXcont : ∀ᵐ ω ∂P, Continuous (X · ω))
    (hXmeas : ∀ t, Measurable (X t)) :
    ∃ Y : Ω → C(Time, State), Measurable Y ∧
      ∀ᵐ ω ∂P, ∀ t, Y ω t = X t ω := by
  let raw : Ω → Time → State := fun ω t => X t ω
  have hraw : Measurable raw :=
    measurable_pi_iff.mpr fun t => hXmeas t
  let f₀ : C(Time, State) := Classical.choice ‹Nonempty C(Time, State)›
  obtain ⟨g, hgMeas, hgContinuous, hrawEq⟩ :=
    hraw.aemeasurable.exists_ae_eq_range_subset hXcont
      ⟨f₀, f₀.continuous⟩
  let gContinuous : Ω → {f : Time → State // Continuous f} :=
    fun ω => ⟨g ω, hgContinuous (Set.mem_range_self ω)⟩
  have hgContinuousMeas : Measurable gContinuous :=
    Measurable.subtype_mk hgMeas
  let pathEquiv := MeasurableEquiv.continuousMapToFun Time State
  refine ⟨fun ω => pathEquiv.symm (gContinuous ω),
    pathEquiv.symm.measurable.comp hgContinuousMeas, ?_⟩
  filter_upwards [hrawEq] with ω hω
  intro t
  change g ω t = X t ω
  exact (congrFun hω t).symm

end ProbabilityTheory

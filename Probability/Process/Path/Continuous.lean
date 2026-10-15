/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Continuous sample paths

The public definitions and theorems in this file are:

- `ProbabilityTheory.continuousPath`: a process with continuous sample
  paths is bundled as an element of $C(\mathrm{Time},\mathrm{State})$.
- `ProbabilityTheory.continuousPath_apply`: evaluation of that bundle
  recovers the original process coordinate.
- `ProbabilityTheory.measurable_continuousPath`: measurable coordinates
  make this continuous-path-valued random variable measurable.
- `ProbabilityTheory.freezeAfter`: the path $u\mapsto f(\min(u,r))$.
- `ProbabilityTheory.measurable_freezeAfter`: freezing at $r$ is a
  measurable operation on continuous path space.
- `ProbabilityTheory.shiftToZero`: the increment path
  $u\mapsto f(r+u)-f(r)$.
- `ProbabilityTheory.measurable_shiftToZero`: the shift is measurable
  jointly in the continuous path and its starting time.

Processes use mathlib's convention `Time → Ω → State`.
-/

@[expose] public section

open scoped NNReal

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

/-- Freeze a continuous path at the value it has at time `r`. -/
noncomputable def freezeAfter (f : C(ℝ≥0, ℝ)) (r : ℝ≥0) : C(ℝ≥0, ℝ) :=
  ⟨fun u => f (min u r), by fun_prop⟩

/-- Rebase a continuous path at time `r`, with initial value zero. -/
noncomputable def shiftToZero (f : C(ℝ≥0, ℝ)) (r : ℝ≥0) : C(ℝ≥0, ℝ) :=
  ⟨fun u => f (r + u) - f r, by fun_prop⟩

/-- The future increment path is jointly measurable in its path and
its starting time. -/
theorem measurable_shiftToZero :
    Measurable (fun p : C(ℝ≥0, ℝ) × ℝ≥0 => shiftToZero p.1 p.2) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro u
  exact (continuous_eval.comp
    (continuous_fst.prodMk (continuous_snd.add continuous_const))).measurable.sub
      (continuous_eval.comp (continuous_fst.prodMk continuous_snd)).measurable

/-- Freezing a continuous path at a fixed time is measurable. -/
theorem measurable_freezeAfter (r : ℝ≥0) :
    Measurable (fun f : C(ℝ≥0, ℝ) => freezeAfter f r) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro u
  exact ContinuousMap.measurable_eval (min u r)

end ProbabilityTheory

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Probability.Process.IndepIncrements.TimeChange
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
- `ProbabilityTheory.IsLevyProcess.map`: if $\varphi:E\to F$ is a continuous,
  measurable additive homomorphism, then $t\mapsto\varphi(X_t)$ is again a
  Lévy process.
- `ProbabilityTheory.IsLevyProcess.comp_time`: if $\tau:\mathbb R_{\ge0}\to
  \mathbb R_{\ge0}$ is a continuous additive homomorphism, then
  $t\mapsto X_{\tau(t)}$ is again a Lévy process.

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

/-- A continuous measurable additive homomorphism of the state space sends a
Lévy process to a Lévy process. -/
theorem map {F : Type*} [AddGroup F] [MeasurableSpace F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [BorelSpace F]
    (h : IsLevyProcess X P) (φ : E →+ F)
    (hφm : Measurable φ) (hφc : Continuous φ) :
    IsLevyProcess (fun t ω => φ (X t ω)) P := by
  refine ⟨?_, h.indepIncrements.map' hφm, ?_, ?_⟩
  · filter_upwards [h.ae_start_eq_zero] with ω hω
    simp [hω]
  · intro s t
    simpa only [Function.comp_def, map_sub] using
      (h.stationaryIncrements s t).comp hφm
  · filter_upwards [h.ae_cadlag] with ω hω
    exact hω.continuous_comp hφc

/-- Composition with a continuous additive homomorphism of nonnegative time
preserves the Lévy-process structure. -/
theorem comp_time (h : IsLevyProcess X P)
    (τ : ℝ≥0 →+ ℝ≥0) (hτc : Continuous τ) :
    IsLevyProcess (fun t ω => X (τ t) ω) P := by
  have hτmono : Monotone τ := by
    intro s t hst
    have hdecomp : s + (t - s) = t := by
      calc
        s + (t - s) = (t - s) + s := add_comm _ _
        _ = t := tsub_add_cancel_of_le hst
    rw [← hdecomp, map_add]
    exact le_add_of_nonneg_right (show 0 ≤ τ (t - s) by positivity)
  refine ⟨?_, h.indepIncrements.comp_time τ hτmono, ?_, ?_⟩
  · filter_upwards [h.ae_start_eq_zero] with ω hω
    simpa using hω
  · intro s t
    simpa only [map_add, AddMonoidHom.map_zero] using
      h.stationaryIncrements (τ s) (τ t)
  · filter_upwards [h.ae_cadlag] with ω hω
    exact hω.comp_monotone_continuous hτmono hτc

end IsLevyProcess

end ProbabilityTheory

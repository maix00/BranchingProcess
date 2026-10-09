/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Probability.Process.Path.Continuous
public import Topology.Order.UnitInterval.Time

/-!
# Continuous paths of processes on the unit interval

This file restricts a continuous real-time process to the canonical unit
interval and bundles the sample paths as continuous maps.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- Restrict a continuous process on nonnegative time to `[0,1]` and bundle
its sample paths as continuous maps. -/
def continuousunitIntervalPath
    (X : NNReal → Ω → ℝ) (hX : ∀ ω, Continuous (X · ω)) :
    Ω → C(unitInterval, ℝ) :=
  continuousPath (fun t ω ↦ X (UnitInterval.toNNReal t) ω)
    fun ω ↦ (hX ω).comp UnitInterval.continuous_toNNReal

@[simp]
theorem continuousunitIntervalPath_apply
    (X : NNReal → Ω → ℝ) (hX : ∀ ω, Continuous (X · ω))
    (ω : Ω) (t : unitInterval) :
    continuousunitIntervalPath X hX ω t = X (UnitInterval.toNNReal t) ω :=
  rfl

theorem measurable_continuousunitIntervalPath [MeasurableSpace Ω]
    (X : NNReal → Ω → ℝ) (hX : ∀ ω, Continuous (X · ω))
    (hXmeas : ∀ t, Measurable (X t)) :
    Measurable (continuousunitIntervalPath X hX) := by
  apply measurable_continuousPath
  intro t
  exact hXmeas (UnitInterval.toNNReal t)

end ProbabilityTheory

end

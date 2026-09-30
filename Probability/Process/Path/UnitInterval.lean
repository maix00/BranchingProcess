module

public import Mathlib.Topology.UnitInterval
public import Probability.Process.Path.Continuous

@[expose] public section

/-!
# Continuous paths on the unit interval

This file contains the restriction of an everywhere-continuous real process
to `[0, 1]`, bundled as a continuous-map-valued random variable. It is a
path-space construction and does not depend on Brownian motion.
-/

open MeasureTheory

namespace ProbabilityTheory

/-- The inclusion of the real unit interval into nonnegative real time. -/
def unitIntervalToNNReal (t : unitInterval) : NNReal :=
  ⟨t, t.property.1⟩

theorem continuous_unitIntervalToNNReal : Continuous unitIntervalToNNReal := by
  exact continuous_subtype_val.subtype_mk _

/-- The identity clock on the compact time horizon `[0, 1]`.  This is a
generic path-time construction; probabilistic process laws may specialize it
to their own increment assumptions. -/
def unitIntervalClock : unitInterval → ℝ := fun t => (t : ℝ)

theorem monotone_unitIntervalClock : Monotone unitIntervalClock := by
  intro s t hst
  exact hst

theorem unitIntervalClock_bot : unitIntervalClock ⊥ = 0 := by
  simp [unitIntervalClock]

/-- Restrict an everywhere-continuous real process to `[0, 1]` and bundle its
sample paths as continuous maps. -/
def continuousunitIntervalPath
    (X : NNReal → Ω → ℝ) (hX : ∀ ω, Continuous (X · ω)) :
    Ω → C(unitInterval, ℝ) :=
  continuousPath (fun t ω ↦ X (unitIntervalToNNReal t) ω)
    fun ω ↦ (hX ω).comp continuous_unitIntervalToNNReal

@[simp]
theorem continuousunitIntervalPath_apply
    (X : NNReal → Ω → ℝ) (hX : ∀ ω, Continuous (X · ω))
    (ω : Ω) (t : unitInterval) :
    continuousunitIntervalPath X hX ω t = X (unitIntervalToNNReal t) ω :=
  rfl

theorem measurable_continuousunitIntervalPath [MeasurableSpace Ω]
    (X : NNReal → Ω → ℝ) (hX : ∀ ω, Continuous (X · ω))
    (hXmeas : ∀ t, Measurable (X t)) :
    Measurable (continuousunitIntervalPath X hX) := by
  apply measurable_continuousPath
  intro t
  exact hXmeas (unitIntervalToNNReal t)

end ProbabilityTheory

end

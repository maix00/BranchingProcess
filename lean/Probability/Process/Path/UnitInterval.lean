/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Probability.Process.Path.Continuous

/-!
# Continuous paths on the unit interval

This file contains the restriction of an everywhere-continuous real process
to `[0, 1]`, bundled as a continuous-map-valued random variable. It is a
path-space construction and does not depend on Brownian motion.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- The inclusion of the real unit interval into nonnegative real time. -/
def unitIntervalToNNReal (t : unitInterval) : NNReal :=
  ⟨t, t.property.1⟩

theorem continuous_unitIntervalToNNReal : Continuous unitIntervalToNNReal := by
  exact continuous_subtype_val.subtype_mk _

@[simp] theorem unitIntervalToNNReal_top : unitIntervalToNNReal ⊤ = 1 := by
  apply NNReal.coe_injective
  rfl

theorem unitIntervalToNNReal_le_one (t : unitInterval) :
    unitIntervalToNNReal t ≤ 1 := by
  apply NNReal.coe_le_coe.mpr
  exact t.property.2

/-- Every point of a nonnegative interval is reached by the normalized
unit-interval clock when the interval has positive length. -/
theorem exists_unitInterval_mul_eq (length t : NNReal)
    (hlength : 0 < length) (ht : t ≤ length) :
    ∃ u : unitInterval, length * unitIntervalToNNReal u = t := by
  have hreal : 0 < (length : ℝ) := NNReal.coe_pos.mpr hlength
  have htle : (t : ℝ) ≤ (length : ℝ) := NNReal.coe_le_coe.mpr ht
  let u : unitInterval := ⟨(t : ℝ) / length, by
    constructor
    · positivity
    · exact (div_le_one hreal).mpr htle⟩
  refine ⟨u, ?_⟩
  apply NNReal.coe_injective
  change (length : ℝ) * ((t : ℝ) / length) = t
  field_simp

/-- Every point of a translated nonnegative interval is reached by its
normalized affine clock. -/
theorem exists_unitInterval_add_mul_eq (start length t : NNReal)
    (hlength : 0 < length) (hstart : start ≤ t)
    (hend : t ≤ start + length) :
    ∃ u : unitInterval, start + length * unitIntervalToNNReal u = t := by
  have hdelta : t - start ≤ length := by
    exact tsub_le_iff_left.mpr hend
  obtain ⟨u, hu⟩ := exists_unitInterval_mul_eq length (t - start)
    hlength hdelta
  refine ⟨u, ?_⟩
  rw [hu]
  simpa [add_comm] using tsub_add_cancel_of_le hstart

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

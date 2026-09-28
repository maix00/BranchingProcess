import Mathlib.Probability.BrownianMotion.Basic
import Probability.Process.Path.Continuous
import Topology.Cadlag.Skorokhod.ContinuousMap

/-!
# Brownian processes in Skorokhod space

This file maps any chosen everywhere-continuous, coordinate-measurable version
of a real process to the Skorokhod path space on `[0, 1]`. In particular it
applies to such a version of any process satisfying mathlib's
`IsBrownianReal` predicate. It does not depend on a particular construction
of Brownian motion.
-/

open MeasureTheory

namespace ProbabilityTheory

/-- The inclusion of the real unit interval into nonnegative real time. -/
def unitIntervalToNNReal (t : Skorokhod.UnitInterval) : NNReal :=
  ⟨t, t.property.1⟩

theorem continuous_unitIntervalToNNReal : Continuous unitIntervalToNNReal := by
  exact continuous_subtype_val.subtype_mk _

/-- Restrict an everywhere-continuous real process to `[0, 1]` and bundle its
sample paths as continuous maps. -/
def continuousUnitIntervalPath
    (X : NNReal → Ω → ℝ) (hX : ∀ ω, Continuous (X · ω)) :
    Ω → C(Skorokhod.UnitInterval, ℝ) :=
  continuousPath (fun t ω ↦ X (unitIntervalToNNReal t) ω)
    fun ω ↦ (hX ω).comp continuous_unitIntervalToNNReal

@[simp]
theorem continuousUnitIntervalPath_apply
    (X : NNReal → Ω → ℝ) (hX : ∀ ω, Continuous (X · ω))
    (ω : Ω) (t : Skorokhod.UnitInterval) :
    continuousUnitIntervalPath X hX ω t = X (unitIntervalToNNReal t) ω :=
  rfl

theorem measurable_continuousUnitIntervalPath [MeasurableSpace Ω]
    (X : NNReal → Ω → ℝ) (hX : ∀ ω, Continuous (X · ω))
    (hXmeas : ∀ t, Measurable (X t)) :
    Measurable (continuousUnitIntervalPath X hX) := by
  apply measurable_continuousPath
  intro t
  exact hXmeas (unitIntervalToNNReal t)

/-- An everywhere-continuous version of a real process, restricted to
`[0, 1]` and regarded as a Skorokhod càdlàg path. -/
def cadlagUnitIntervalPath
    (X : NNReal → Ω → ℝ) (hX : ∀ ω, Continuous (X · ω)) :
    Ω → CadlagPath Skorokhod.UnitInterval ℝ :=
  fun ω ↦ Skorokhod.ofContinuousMap (continuousUnitIntervalPath X hX ω)

@[simp]
theorem cadlagUnitIntervalPath_apply
    (X : NNReal → Ω → ℝ) (hX : ∀ ω, Continuous (X · ω))
    (ω : Ω) (t : Skorokhod.UnitInterval) :
    cadlagUnitIntervalPath X hX ω t = X (unitIntervalToNNReal t) ω :=
  rfl

theorem measurable_cadlagUnitIntervalPath [MeasurableSpace Ω]
    (X : NNReal → Ω → ℝ) (hX : ∀ ω, Continuous (X · ω))
    (hXmeas : ∀ t, Measurable (X t)) :
    Measurable (cadlagUnitIntervalPath X hX) :=
  Skorokhod.measurable_ofContinuousMap.comp
    (measurable_continuousUnitIntervalPath X hX hXmeas)

/-- The Skorokhod path law of a chosen continuous version. -/
noncomputable def cadlagUnitIntervalPathLaw [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → ℝ)
    (hX : ∀ ω, Continuous (X · ω))
    (_hXmeas : ∀ t, Measurable (X t)) :
    Measure (CadlagPath Skorokhod.UnitInterval ℝ) :=
  P.map (cadlagUnitIntervalPath X hX)

noncomputable instance cadlagUnitIntervalPathLaw.instIsProbabilityMeasure
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : ∀ ω, Continuous (X · ω))
    (hXmeas : ∀ t, Measurable (X t)) :
    IsProbabilityMeasure (cadlagUnitIntervalPathLaw P X hX hXmeas) := by
  unfold cadlagUnitIntervalPathLaw
  infer_instance

theorem hasLaw_cadlagUnitIntervalPath [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → ℝ)
    (hX : ∀ ω, Continuous (X · ω))
    (hXmeas : ∀ t, Measurable (X t)) :
    HasLaw (cadlagUnitIntervalPath X hX)
      (cadlagUnitIntervalPathLaw P X hX hXmeas) P where
  aemeasurable := (measurable_cadlagUnitIntervalPath X hX hXmeas).aemeasurable
  map_eq := rfl

/-- A chosen continuous measurable version of a Brownian process has the
abstract Skorokhod path law above. -/
theorem IsBrownianReal.hasLaw_cadlagUnitIntervalPath [MeasurableSpace Ω]
    {P : Measure Ω} {X : NNReal → Ω → ℝ} (_hB : IsBrownianReal X P)
    (hX : ∀ ω, Continuous (X · ω))
    (hXmeas : ∀ t, Measurable (X t)) :
    HasLaw (cadlagUnitIntervalPath X hX)
      (cadlagUnitIntervalPathLaw P X hX hXmeas) P :=
  ProbabilityTheory.hasLaw_cadlagUnitIntervalPath P X hX hXmeas

end ProbabilityTheory

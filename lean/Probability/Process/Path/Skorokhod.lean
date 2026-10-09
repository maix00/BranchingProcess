/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.HasLaw
public import Probability.Process.Path.UnitInterval
public import Topology.Cadlag.Skorokhod.ContinuousMap

/-!
# Càdlàg path-space interfaces

The canonical coordinate process and the embedding of continuous
unit-interval paths into Skorokhod space are generic path-space interfaces.
The path-space embedding and its law apply to any everywhere-continuous,
coordinate-measurable real process. Brownian finite-dimensional identities are
proved in the Brownian layer.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

/-- The canonical coordinate process on càdlàg paths over an ordered
topological time axis.  It is independent of any particular process law. -/
def cadlagPathProcess {Time E : Type*} [PartialOrder Time] [TopologicalSpace Time]
    [TopologicalSpace E] :
    Time → CadlagPath Time E → E := fun t f => f t

@[simp]
theorem cadlagPathProcess_apply {Time E : Type*} [PartialOrder Time]
    [TopologicalSpace Time] [TopologicalSpace E]
    (t : Time) (f : CadlagPath Time E) :
    cadlagPathProcess t f = f t := rfl

/-- An everywhere-continuous version of a real process, restricted to
`[0, 1]` and regarded as a Skorokhod càdlàg path. -/
def cadlagunitIntervalPath
    (X : NNReal → Ω → ℝ) (hX : ∀ ω, Continuous (X · ω)) :
    Ω → CadlagPath unitInterval ℝ :=
  fun ω ↦ Skorokhod.ofContinuousMap (continuousunitIntervalPath X hX ω)

@[simp]
theorem cadlagunitIntervalPath_apply
    (X : NNReal → Ω → ℝ) (hX : ∀ ω, Continuous (X · ω))
    (ω : Ω) (t : unitInterval) :
    cadlagunitIntervalPath X hX ω t = X (UnitInterval.toNNReal t) ω :=
  rfl

theorem measurable_cadlagunitIntervalPath [MeasurableSpace Ω]
    (X : NNReal → Ω → ℝ) (hX : ∀ ω, Continuous (X · ω))
    (hXmeas : ∀ t, Measurable (X t)) :
    Measurable (cadlagunitIntervalPath X hX) :=
  Skorokhod.measurable_ofContinuousMap.comp
    (measurable_continuousunitIntervalPath X hX hXmeas)

/-- The Skorokhod path law of a chosen continuous version. -/
noncomputable def cadlagunitIntervalPathLaw [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → ℝ)
    (hX : ∀ ω, Continuous (X · ω))
    (_hXmeas : ∀ t, Measurable (X t)) :
    Measure (CadlagPath unitInterval ℝ) :=
  P.map (cadlagunitIntervalPath X hX)

noncomputable instance cadlagunitIntervalPathLaw.instIsProbabilityMeasure
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : ∀ ω, Continuous (X · ω))
    (hXmeas : ∀ t, Measurable (X t)) :
    IsProbabilityMeasure (cadlagunitIntervalPathLaw P X hX hXmeas) := by
  unfold cadlagunitIntervalPathLaw
  infer_instance

theorem hasLaw_cadlagunitIntervalPath [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → ℝ)
    (hX : ∀ ω, Continuous (X · ω))
    (hXmeas : ∀ t, Measurable (X t)) :
    HasLaw (cadlagunitIntervalPath X hX)
      (cadlagunitIntervalPathLaw P X hX hXmeas) P where
  aemeasurable := (measurable_cadlagunitIntervalPath X hX hXmeas).aemeasurable
  map_eq := rfl

end ProbabilityTheory

end

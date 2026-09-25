import Probability.BranchingRandomWalk.PointProcess.Representation.RankedReconstruction
import Combinatorics.BranchingStep.Slot.Basic
import Probability.BranchingRandomWalk.PointProcess.Representation.MonotoneEnumeration

/-!
# Canonical monotone enumeration of an abstract point process

Every abstract point process whose sample measures are counting measures and
are left-locally finite has a canonical measurable monotone slot enumeration,
obtained by applying the ranked construction samplewise. This file contains
only the sample-space wrapper; the deterministic ranked construction is in
`Representation/RankedReconstruction.lean`.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



/-- The canonical measurable ordered mark attached to an abstract
branching-step point process. -/
noncomputable def canonicalStep
    {Ω : Type*} [MeasurableSpace Ω] (Ξ : RealStepPointProcess Ω) :
    Ω → NatRealStep :=
  fun ω => measureToStep (Ξ ω)

theorem canonicalStep_measurable
    {Ω : Type*} [MeasurableSpace Ω] (Ξ : RealStepPointProcess Ω) :
    Measurable (canonicalStep Ξ) :=
  measureToStep_measurable.comp Ξ.measurable_toMeasure

theorem canonicalStep_ordered
    {Ω : Type*} [MeasurableSpace Ω] (Ξ : RealStepPointProcess Ω)
    (ω : Ω) : canonicalStep Ξ ω ∈ orderedSteps :=
  measureToStep_ordered (Ξ ω) (Ξ.counting ω)
    (Ξ.finiteOn ω)

theorem canonicalStep_nonempty_iff
    {Ω : Type*} [MeasurableSpace Ω] (Ξ : RealStepPointProcess Ω)
    (ω : Ω) :
    canonicalStep Ξ ω ∈ childNonempty ↔ Ξ ω ≠ 0 :=
  measureToStep_nonempty_iff (Ξ ω) (Ξ.counting ω)

/-- Every abstract point process satisfying the foundational counting and
left-local-finiteness fields has a canonical measurable monotone optional-slot
representation. -/
noncomputable def canonicalMonotoneEnumeration
    {Ω : Type*} [MeasurableSpace Ω] (Ξ : RealStepPointProcess Ω) :
    MonotoneEnumeration (X := ℝ) Ξ (· ≤ ·) where
  toStep := canonicalStep Ξ
  measurable_toStep := canonicalStep_measurable Ξ
  presence_prefix := fun ω => (canonicalStep_ordered Ξ ω).1
  rel_ordered := fun ω => (canonicalStep_ordered Ξ ω).2
  measure_eq := fun ω =>
    stepPointMeasure_measureToStep_eq (Ξ ω)
      (Ξ.counting ω) (Ξ.finiteOn ω)

/-- Applying the canonical enumeration to a measurable random measure remains
measurable. -/
theorem measureToStep_comp_measurable
    {Ω : Type*} [MeasurableSpace Ω] (Ξ : RealStepPointProcess Ω) :
    Measurable (fun ω => measureToStep (Ξ ω)) :=
  measureToStep_measurable.comp Ξ.measurable_toMeasure

end ProbabilityTheory.BranchingRandomWalk

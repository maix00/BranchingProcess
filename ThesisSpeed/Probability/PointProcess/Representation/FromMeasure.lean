import ThesisSpeed.Probability.PointProcess.Representation.RankedEnumeration
import ThesisSpeed.Probability.PointProcess.Representation.MonotoneEnumeration

/-!
# Canonical monotone enumeration of an abstract point process

Every abstract point process whose sample measures are counting measures and
are left-locally finite has a canonical measurable monotone slot enumeration,
obtained by applying the ranked construction samplewise. This file contains
only the sample-space wrapper; the deterministic ranked construction is in
`Representation/RankedEnumeration.lean`.
-/

open MeasureTheory

namespace ThesisSpeed

/-- The canonical measurable ordered mark attached to an abstract
branching-step point process. -/
noncomputable def canonicalBranchingStep
    {Ω : Type*} [MeasurableSpace Ω] (Ξ : RealBranchingStepPointProcess Ω) :
    Ω → NatRealBranchingStep :=
  fun ω => measureToBranchingStep (Ξ ω)

theorem canonicalBranchingStep_measurable
    {Ω : Type*} [MeasurableSpace Ω] (Ξ : RealBranchingStepPointProcess Ω) :
    Measurable (canonicalBranchingStep Ξ) :=
  measureToBranchingStep_measurable.comp Ξ.measurable_toMeasure

theorem canonicalBranchingStep_ordered
    {Ω : Type*} [MeasurableSpace Ω] (Ξ : RealBranchingStepPointProcess Ω)
    (ω : Ω) : canonicalBranchingStep Ξ ω ∈ orderedBranchingSteps :=
  measureToBranchingStep_ordered (Ξ ω) (Ξ.counting ω)
    (Ξ.finiteOn ω)

theorem canonicalBranchingStep_nonempty_iff
    {Ω : Type*} [MeasurableSpace Ω] (Ξ : RealBranchingStepPointProcess Ω)
    (ω : Ω) :
    canonicalBranchingStep Ξ ω ∈ childNonempty ↔ Ξ ω ≠ 0 :=
  measureToBranchingStep_nonempty_iff (Ξ ω) (Ξ.counting ω)

/-- Every abstract point process satisfying the foundational counting and
left-local-finiteness fields has a canonical measurable monotone optional-slot
representation. -/
noncomputable def canonicalMonotoneEnumeration
    {Ω : Type*} [MeasurableSpace Ω] (Ξ : RealBranchingStepPointProcess Ω) :
    MonotoneEnumeration (X := ℝ) Ξ (· ≤ ·) where
  toStep := canonicalBranchingStep Ξ
  measurable_toStep := canonicalBranchingStep_measurable Ξ
  presence_prefix := fun ω => (canonicalBranchingStep_ordered Ξ ω).1
  rel_ordered := fun ω => (canonicalBranchingStep_ordered Ξ ω).2
  measure_eq := fun ω =>
    branchingStepPointMeasure_measureToBranchingStep_eq (Ξ ω)
      (Ξ.counting ω) (Ξ.finiteOn ω)

/-- Applying the canonical enumeration to a measurable random measure remains
measurable. -/
theorem measureToBranchingStep_comp_measurable
    {Ω : Type*} [MeasurableSpace Ω] (Ξ : RealBranchingStepPointProcess Ω) :
    Measurable (fun ω => measureToBranchingStep (Ξ ω)) :=
  measureToBranchingStep_measurable.comp Ξ.measurable_toMeasure

end ThesisSpeed

import ThesisSpeed.Probability.PointProcess.Slot.PointMeasure
import ThesisSpeed.Probability.PointProcess.Slot.Order

/-!
# Structural assumptions on the child law

These predicates mirror the structural assumptions stated in the thesis.
They are kept separate from moment assumptions so that individual theorems
can request only what their proofs use.
-/

open MeasureTheory
open scoped ENNReal

namespace ThesisSpeed

/-- The child law has at least one child almost surely. -/
def HasAtLeastOneChild (μ : Measure NatRealBranchingStep) : Prop :=
  μ childNonempty = 1

/-- The concrete slots are an ordered enumeration of the child atoms. -/
def HasOrderedSlots (μ : Measure NatRealBranchingStep) : Prop :=
  μ orderedBranchingSteps = 1

/-- Expected child count, expressed through the point-measure mass. -/
noncomputable def expectedChildCount
    (μ : Measure NatRealBranchingStep) : ENNReal :=
  ∫⁻ ξ, branchingStepPointMeasure ξ Set.univ ∂μ

/-- The supercritical assumption `E[#Ξ] > 1`. -/
def IsSupercriticalBranchingLaw (μ : Measure NatRealBranchingStep) : Prop :=
  1 < expectedChildCount μ

/-- The boundary normalization `E[∑ exp(-Ξᵢ)] = 1`. -/
def HasBoundaryNormalization (μ : Measure NatRealBranchingStep) : Prop :=
  ∫⁻ ξ, totalChildWeight ξ ∂μ = 1

theorem hasAtLeastOneChild_ae (μ : Measure NatRealBranchingStep)
    [IsProbabilityMeasure μ] (h : HasAtLeastOneChild μ) :
    ∀ᵐ ξ ∂μ, ξ ∈ childNonempty := by
  exact (ae_mem_iff_measure_eq childNonempty_measurable.nullMeasurableSet).2
    (by simpa [HasAtLeastOneChild] using h)

end ThesisSpeed

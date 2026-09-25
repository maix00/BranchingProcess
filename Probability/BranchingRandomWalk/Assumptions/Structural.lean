import Probability.BranchingRandomWalk.PointProcess.PointMeasure
import Combinatorics.BranchingStep.Slot.Basic
import Combinatorics.BranchingStep.Slot.Order

/-!
# Structural assumptions on the child law

These predicates mirror the structural assumptions stated in the thesis.
They are kept separate from moment assumptions so that individual theorems
can request only what their proofs use.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



/-- The child law has at least one child almost surely. -/
def HasAtLeastOneChild (μ : Measure NatRealStep) : Prop :=
  μ childNonempty = 1

/-- The concrete slots are an ordered enumeration of the child atoms. -/
def HasOrderedSlots (μ : Measure NatRealStep) : Prop :=
  μ orderedSteps = 1

/-- Expected child count, expressed through the point-measure mass. -/
noncomputable def expectedChildCount
    (μ : Measure NatRealStep) : ENNReal :=
  ∫⁻ ξ, stepPointMeasure ξ Set.univ ∂μ

/-- The supercritical assumption `E[#Ξ] > 1`. -/
def IsSupercriticalBranchingLaw (μ : Measure NatRealStep) : Prop :=
  1 < expectedChildCount μ

/-- The boundary normalization `E[∑ exp(-Ξᵢ)] = 1`. -/
def HasBoundaryNormalization (μ : Measure NatRealStep) : Prop :=
  ∫⁻ ξ, totalChildWeight ξ ∂μ = 1

theorem hasAtLeastOneChild_ae (μ : Measure NatRealStep)
    [IsProbabilityMeasure μ] (h : HasAtLeastOneChild μ) :
    ∀ᵐ ξ ∂μ, ξ ∈ childNonempty := by
  exact (ae_mem_iff_measure_eq childNonempty_measurable.nullMeasurableSet).2
    (by simpa [HasAtLeastOneChild] using h)

end ProbabilityTheory.BranchingRandomWalk

import ThesisSpeed.Probability.PointProcess.Measure
import ThesisSpeed.Probability.PointProcess.Enumeration.Order

/-!
# Structural assumptions on the offspring law

These predicates mirror the structural assumptions stated in the thesis.
They are kept separate from moment assumptions so that individual theorems
can request only what their proofs use.
-/

open MeasureTheory
open scoped ENNReal

namespace ThesisSpeed

/-- The offspring law has at least one child almost surely. -/
def HasAtLeastOneChild (μ : Measure OffspringMark) : Prop :=
  μ offspringNonempty = 1

/-- The concrete slots are an ordered enumeration of the offspring atoms. -/
def HasOrderedOffspring (μ : Measure OffspringMark) : Prop :=
  μ orderedOffspring = 1

/-- Expected offspring count, expressed through the point-measure mass. -/
noncomputable def expectedOffspringCount
    (μ : Measure OffspringMark) : ENNReal :=
  ∫⁻ ξ, offspringPointMeasure ξ Set.univ ∂μ

/-- The supercritical assumption `E[#Ξ] > 1`. -/
def IsSupercriticalOffspringLaw (μ : Measure OffspringMark) : Prop :=
  1 < expectedOffspringCount μ

/-- The boundary normalization `E[∑ exp(-Ξᵢ)] = 1`. -/
def HasBoundaryNormalization (μ : Measure OffspringMark) : Prop :=
  ∫⁻ ξ, totalChildWeight ξ ∂μ = 1

theorem hasAtLeastOneChild_ae (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] (h : HasAtLeastOneChild μ) :
    ∀ᵐ ξ ∂μ, ξ ∈ offspringNonempty := by
  exact (ae_mem_iff_measure_eq offspringNonempty_measurable.nullMeasurableSet).2
    (by simpa [HasAtLeastOneChild] using h)

end ThesisSpeed

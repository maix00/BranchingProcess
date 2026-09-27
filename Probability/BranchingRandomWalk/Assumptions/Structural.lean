import Probability.BranchingRandomWalk.PointProcess.PointMeasure
import Combinatorics.BranchingWalk.Step.Measurability
import Combinatorics.BranchingWalk.Step.Monotone

/-!
# Structural assumptions on the child law

These predicates mirror the structural assumptions stated in the thesis.
They are kept separate from moment assumptions so that individual theorems
can request only what their proofs use.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



/-- The child law has at least one child almost surely. -/
def HasAtLeastOneChild (μ : Measure (Step ℕ ℝ)) : Prop :=
  μ nonemptySupport = 1

/-- The concrete slots are an ordered enumeration of the child atoms. -/
def HasOrderedSlots (μ : Measure (Step ℕ ℝ)) : Prop :=
  μ orderedSteps = 1

/-- Expected child count, expressed through the point-measure mass. -/
noncomputable def expectedChildCount
    (μ : Measure (Step ℕ ℝ)) : ENNReal :=
  ∫⁻ ξ, stepPointMeasure ξ Set.univ ∂μ

/-- The supercritical assumption `E[#Ξ] > 1`. -/
def IsSupercriticalBranchingLaw (μ : Measure (Step ℕ ℝ)) : Prop :=
  1 < expectedChildCount μ

/-- The boundary normalization `E[∑ exp(-Ξᵢ)] = 1`. -/
def HasBoundaryNormalization (μ : Measure (Step ℕ ℝ)) : Prop :=
  ∫⁻ ξ, totalChildWeight ξ ∂μ = 1

theorem hasAtLeastOneChild_ae (μ : Measure (Step ℕ ℝ))
    [IsProbabilityMeasure μ] (h : HasAtLeastOneChild μ) :
    ∀ᵐ ξ ∂μ, ξ ∈ nonemptySupport := by
  exact (ae_mem_iff_measure_eq nonemptySupport_measurable.nullMeasurableSet).2
    (by simpa [HasAtLeastOneChild] using h)

end ProbabilityTheory.BranchingRandomWalk

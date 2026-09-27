import Probability.BranchingRandomWalk.PointProcess.PointMeasure
import Combinatorics.BranchingWalk.Step.Measurability
import Combinatorics.BranchingWalk.Step.Monotone

/-!
# Structural assumptions on the child law

These predicates mirror the structural assumptions stated in the thesis. The slot type and the mark type are
arbitrary — a law is about the steps it supports, not about `ℕ` or `ℝ` — and only the boundary normalization
needs real marks, because it sums the exponential child weight. The predicates are kept separate from moment
assumptions so that individual theorems can request only what their proofs use.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



/-- The child law has at least one child almost surely. -/
def HasAtLeastOneChild {α X : Type*} [MeasurableSpace X] (μ : Measure (Step α X)) : Prop :=
  μ nonemptySupport = 1

/-- The concrete slots are an ordered enumeration of the child atoms. -/
def HasOrderedSlots {α X : Type*} [LT α] [LE X] [MeasurableSpace X]
    (μ : Measure (Step α X)) : Prop :=
  μ orderedSteps = 1

/-- Expected child count, expressed through the point-measure mass. -/
noncomputable def expectedChildCount {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) : ENNReal :=
  ∫⁻ ξ, stepPointMeasure ξ Set.univ ∂μ

/-- The supercritical assumption `E[#Ξ] > 1`. -/
def IsSupercriticalBranchingLaw {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) : Prop :=
  1 < expectedChildCount μ

/-- The boundary normalization `E[∑ exp(-Ξᵢ)] = 1`. -/
def HasBoundaryNormalization (μ : Measure (Step ℕ ℝ)) : Prop :=
  ∫⁻ ξ, totalChildWeight ξ ∂μ = 1

theorem hasAtLeastOneChild_ae {α X : Type*} [Countable α] [MeasurableSpace X]
    (μ : Measure (Step α X))
    [IsProbabilityMeasure μ] (h : HasAtLeastOneChild μ) :
    ∀ᵐ ξ ∂μ, ξ ∈ nonemptySupport := by
  exact (ae_mem_iff_measure_eq nonemptySupport_measurable.nullMeasurableSet).2
    (by simpa [HasAtLeastOneChild] using h)

end ProbabilityTheory.BranchingRandomWalk

module

public import Probability.BranchingRandomWalk.Step.PointMeasure
public import Probability.BranchingRandomWalk.Step.OrderingLaw
public import Combinatorics.BranchingWalk.Step.Measurability
public import Combinatorics.BranchingWalk.Step.Monotone

/-!
# Structural assumptions on the child law

These predicates mirror the structural assumptions stated in the thesis. A
raw law is never assumed to have ordered slots. Indexed children are read from
the sorted pushforward supplied by `StepLaw.ordering`.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching MeasureTheory



/-- The child law has at least one child almost surely. -/
def HasAtLeastOneChild {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Combinatorics.Branching.Step α X)) : Prop :=
  μ nonemptySupport = 1

/-- Expected child count, expressed through the point-measure mass. -/
noncomputable def expectedChildCount {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Combinatorics.Branching.Step α X)) : ENNReal :=
  ∫⁻ ξ, stepPointMeasure ξ Set.univ ∂μ

/-- The supercritical assumption `E[#Ξ] > 1`. -/
def IsSupercriticalBranchingLaw {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Combinatorics.Branching.Step α X)) : Prop :=
  1 < expectedChildCount μ

/-- The boundary normalization `E[∑ exp(-Ξᵢ)] = 1`. This sum is invariant
under slot permutations, so it is evaluated directly on the raw law. -/
def HasBoundaryNormalization {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X)
    (μ : Measure (Combinatorics.Branching.Step ι X)) : Prop :=
  ∫⁻ ξ, totalPotentialWeight φ (-1) ξ ∂μ = 1

/-- Boundary normalization forces the negative exponential offspring weight
to be finite almost surely. -/
theorem HasBoundaryNormalization.ae_totalPotentialWeight_ne_top
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (h : HasBoundaryNormalization φ μ) :
    ∀ᵐ ξ ∂μ, totalPotentialWeight φ (-1) ξ ≠ ∞ := by
  have hintegral :
      (∫⁻ ξ, totalPotentialWeight φ (-1) ξ ∂μ) ≠ ∞ := by
    rw [h]
    exact ENNReal.one_ne_top
  filter_upwards [ae_lt_top
    (totalPotentialWeight_measurable φ (-1)) hintegral] with ξ hξ
  exact hξ.ne

theorem hasAtLeastOneChild_ae {α X : Type*} [Countable α] [MeasurableSpace X]
    (μ : Measure (Combinatorics.Branching.Step α X))
    [IsProbabilityMeasure μ] (h : HasAtLeastOneChild μ) :
    ∀ᵐ ξ ∂μ, ξ ∈ nonemptySupport := by
  exact (ae_mem_iff_measure_eq nonemptySupport_measurable.nullMeasurableSet).2
    (by simpa [HasAtLeastOneChild] using h)

end ProbabilityTheory.BranchingRandomWalk

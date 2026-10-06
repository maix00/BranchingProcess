/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.ExponentialWeight

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

end ProbabilityTheory.BranchingRandomWalk

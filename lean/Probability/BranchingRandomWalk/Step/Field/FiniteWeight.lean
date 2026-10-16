/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Assumptions.Structural
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law

/-!
# Almost-sure finite exponential weights in pre-sampled fields

Boundary normalization first gives one-step almost-sure finiteness.  For
countable root and address labels, the same property holds simultaneously at
every coordinate of the root-indexed product field.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

/-- The measurable one-step event on which the negative exponential child
weight is finite. -/
def finitePotentialWeightSteps {α X : Type*} [MeasurableSpace X]
    (φ : Potential X) : Set (Combinatorics.Branching.Step α X) :=
  {ξ | totalPotentialWeight φ (-1) ξ ≠ ∞}

theorem measurableSet_finitePotentialWeightSteps
    {α X : Type*} [Countable α] [MeasurableSpace X]
    (φ : Potential X) : MeasurableSet (finitePotentialWeightSteps (α := α) φ) := by
  exact (totalPotentialWeight_measurable φ (-1)
    (measurableSet_singleton (∞ : ENNReal))).compl

theorem HasBoundaryNormalization.measure_finitePotentialWeightSteps
    {α X : Type*} [Countable α] [MeasurableSpace X]
    (φ : Potential X)
    (μ : Measure (Combinatorics.Branching.Step α X)) [IsProbabilityMeasure μ]
    (h : HasBoundaryNormalization φ μ) :
    μ (finitePotentialWeightSteps φ) = 1 := by
  calc
    μ (finitePotentialWeightSteps φ) = μ Set.univ :=
      (ae_mem_iff_measure_eq
        (measurableSet_finitePotentialWeightSteps φ).nullMeasurableSet).mp
        (by
          change ∀ᵐ ξ ∂μ, totalPotentialWeight φ (-1) ξ ≠ ∞
          exact h.ae_totalPotentialWeight_ne_top φ μ)
    _ = 1 := measure_univ

/-- Under boundary normalization every coordinate of a countably labelled
pre-sampled forest has finite negative exponential weight simultaneously,
almost surely. -/
theorem RootIndexed.stepFieldLaw_all_finitePotentialWeight
    {Root α X : Type*} [Countable Root] [Countable α] [MeasurableSpace X]
    (φ : Potential X)
    (μ : Measure (Combinatorics.Branching.Step α X)) [IsProbabilityMeasure μ]
    (h : HasBoundaryNormalization φ μ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      ∀ r : Root, ∀ u : TreeNode α,
        totalPotentialWeight φ (-1) (field r u) ≠ ∞ := by
  simpa [finitePotentialWeightSteps] using
    (RootIndexed.stepFieldLaw_ae_all_of_measure_one
      (measurableSet_finitePotentialWeightSteps φ) μ
      (h.measure_finitePotentialWeightSteps φ μ))

end ProbabilityTheory.BranchingRandomWalk

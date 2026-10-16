/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Law.SelectedPopulationCausal
import Probability.BranchingRandomWalk.Selection.NSelection.Law.Restarted

/-!
# Coupling first-N populations from nested root sets

The first-N process from a subset of roots is a causal source with at most
`N` particles at every positive generation.  The rank-installed coupling
therefore compares it with first-N selection from a containing root set.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

/-- First-N selection from a subset of roots admits an almost-sure
rank-installed injection into first-N selection from the containing root
set.  The only offspring-law hypothesis is boundary normalization, used by
the existing admissibility theorem for the target selector. -/
theorem RootIndexed.selectedPopulationNestedRootsCoupledInjection_ae
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (sourceRoots targetRoots : Finset Root)
    (hroots : sourceRoots ⊆ targetRoots)
    (initialPosition : Root → ℝ) (n : ℕ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      Nonempty (Cloud.SliceDominatingMap id
        (Combinatorics.Branching.Selection.Coupling.populationCloud id
          (RootIndexed.BranchingWalk.ofStepField initialPosition
            (RootIndexed.StepField.left field))
          (RootIndexed.selectedPopulationTotalized N sourceRoots initialPosition
            id id n (RootIndexed.StepField.left field)))
        (Combinatorics.Branching.Selection.Coupling.populationCloud id
          (RootIndexed.BranchingWalk.ofStepField initialPosition
            (RootIndexed.restartedRealPositionMatchedField N targetRoots
              initialPosition id
              (fun k field => RootIndexed.selectedPopulationTotalized N
                sourceRoots initialPosition id id k
                (RootIndexed.StepField.left field)) n field))
          (RootIndexed.restartedRealPositionMatchedPopulation N targetRoots
            initialPosition id
            (fun k field => RootIndexed.selectedPopulationTotalized N
              sourceRoots initialPosition id id k
              (RootIndexed.StepField.left field)) n field)) ()) := by
  let source := RootIndexed.selectedPopulationTotalizedSource
    (Root := Root) (α := α) (Mark := ℝ) (Position := ℝ) (Value := ℝ)
    N sourceRoots initialPosition id measurable_id id measurable_id
  let hsourceFinite := RootIndexed.selectedPopulationTotalizedSource_finiteSlices
    (Root := Root) (α := α) (Mark := ℝ) (Position := ℝ) (Value := ℝ)
    N sourceRoots initialPosition id measurable_id id measurable_id
  have hsourceEq : hsourceFinite.toFinset =
      (fun k field => RootIndexed.selectedPopulationTotalized N sourceRoots
        initialPosition id id k (RootIndexed.StepField.left field)) := by
    funext k
    funext field
    apply Finset.coe_injective
    rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
    change (source.toPopulation field).particles k = _
    rfl
  have hinitial : ∀ field, Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field))
        (hsourceFinite.toFinset 0 field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.right field))
        (RootIndexed.restartedRealPositionMatchedPopulation N targetRoots
          initialPosition id (hsourceFinite.toFinset) 0 field)) () := by
    intro field
    have hzero : hsourceFinite.toFinset 0 field =
        RootIndexed.initialPopulation (α := α) sourceRoots := by
      apply Finset.coe_injective
      rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
      change (source.toPopulation field).particles 0 = _
      simp [source, RootIndexed.selectedPopulationTotalizedSource,
        RootIndexed.selectedPopulationTotalized]
    rw [hzero]
    simpa [RootIndexed.restartedRealPositionMatchedPopulation,
      RootIndexed.restartedRealPositionMatchedField,
      RootIndexed.selectedPopulationTotalized] using
      (RootIndexed.initialPopulationInjectionOfSubset
        (α := α) (Mark := ℝ) id id initialPosition sourceRoots targetRoots
        hroots (RootIndexed.StepField.left field)
          (RootIndexed.StepField.right field))
  have hgeneric := RootIndexed.restartedRealPositionCoupledInjection_ae
    μ hnorm N targetRoots initialPosition source hsourceFinite hinitial n
  filter_upwards [hgeneric] with field hgood
  have hcapacity : ∀ k < n, (hsourceFinite.toFinset (k + 1) field).card ≤ N := by
    intro k hk
    have hcard := RootIndexed.selectedPopulationTotalized_card_le
      N sourceRoots initialPosition id id k (RootIndexed.StepField.left field)
    simpa [hsourceEq] using hcard
  have hmap := hgood hcapacity
  simpa only [hsourceEq] using hmap

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

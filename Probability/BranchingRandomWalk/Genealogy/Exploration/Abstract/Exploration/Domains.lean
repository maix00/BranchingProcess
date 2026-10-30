/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.Exploration.Space

/-!
# Exploration domains and fresh subtrees

## Public declarations

An exploration domain is a monotone inspected set together with a filtration
bounded by the coordinates on it. Descendant subtrees rooted in fresh addresses
are independent of it.

- `BranchingExplorationDomains α X` packages inspected sets `D_j` and domain
  sigma-algebras `𝓖_j` satisfying `𝓖_j ≤ stepsOnSpace(D_j)` and
  `D_j ⊆ D_{j+1}`.
- `BranchingExplorationDomains.fresh_descendant_independent` states that
  disjointness of `D_j` from the descendants of `u` implies independence of
  `𝓖_j` and the descendant-coordinate sigma-algebra.
- `BranchingExplorationDomains.fresh_subtree_independent` gives the same
  conclusion for the random subtree field `ω ↦ (v ↦ ω (u ++ v))`.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


structure BranchingExplorationDomains
    (α X : Type*) [MeasurableSpace X] where
  inspected : ℕ → Set (TreeNode α)
  domain : ℕ → MeasurableSpace (TreeNode α → Step α X)
  domain_le : ∀ j, domain j ≤ stepsOnSpace (inspected j)
  inspected_mono : Monotone inspected

theorem BranchingExplorationDomains.fresh_descendant_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (H : BranchingExplorationDomains α X) (j : ℕ) (root : TreeNode α)
    (hfresh : Disjoint (H.inspected j)
      (branchingDescendantAddresses root)) :
    Indep (H.domain j) (stepDescendantSpace root)
      (offspringFieldLaw μ) := by
  apply indep_of_indep_of_le_left
    (stepsOnSpace_descendant_independent μ
      (H.inspected j) root hfresh)
  exact H.domain_le j

theorem BranchingExplorationDomains.fresh_subtree_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (H : BranchingExplorationDomains α X) (j : ℕ) (root : TreeNode α)
    (hfresh : Disjoint (H.inspected j)
      (branchingDescendantAddresses root)) :
    Indep (H.domain j)
      (MeasurableSpace.comap (subtreeStepField root) inferInstance)
      (offspringFieldLaw μ) :=
  indep_of_indep_of_le_right
    (H.fresh_descendant_independent μ j root hfresh)
    (subtreeStepField_descendant_measurable root).comap_le

end ProbabilityTheory.BranchingRandomWalk

end

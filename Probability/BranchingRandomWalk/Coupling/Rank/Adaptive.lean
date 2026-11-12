/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Coupling.Rank.Block.Basic
public import Probability.BranchingRandomWalk.Coupling.Field.Law

/-!
# Product law for adaptive rank splicing

The past-measurable rank choice preserves the partner root-indexed product law.

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.Coupling.RootIndexed.stepFieldLaw_spliceByRank`:
  if all objects to match have depth $n$ and the equal-rank choice is countably
  ranged and measurable with respect to generation $n$'s past field, then
  splicing that choice into an independent two-root product field preserves
  the partner product-field law.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Coupling


open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection

/-- A past-measurable equal-rank matching of generation-`n` populations
preserves the complete partner product law. Countability is localized to the
actual range of the random chosen family. -/
theorem RootIndexed.stepFieldLaw_spliceByRank
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (n : ℕ)
    (objectOrderKey partnerOrderKey :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (hobjectsToMatchDepth : ∀ field p, p ∈ objectsToMatch field → p.2.length = n)
    (hcount : (Set.range
      (RootIndexed.rankChoice n objectOrderKey partnerOrderKey objectsToMatch availablePartners)).Countable)
    (hfiber : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field |
        RootIndexed.rankChoice n objectOrderKey partnerOrderKey objectsToMatch availablePartners field =
          roots}) :
    (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (RootIndexed.StepField.splice n
          (RootIndexed.rankChoice n objectOrderKey partnerOrderKey objectsToMatch availablePartners)) =
      RootIndexed.stepFieldLaw (Root := Root) μ := by
  exact RootIndexed.stepFieldLaw_splice μ n
    (RootIndexed.rankChoice n objectOrderKey partnerOrderKey objectsToMatch availablePartners)
    hcount hfiber
    (RootIndexed.rankChoice_depth n objectOrderKey partnerOrderKey objectsToMatch availablePartners
      hobjectsToMatchDepth)
    (RootIndexed.rankChoice_injective n objectOrderKey partnerOrderKey objectsToMatch availablePartners)

end ProbabilityTheory.BranchingRandomWalk.Coupling

end

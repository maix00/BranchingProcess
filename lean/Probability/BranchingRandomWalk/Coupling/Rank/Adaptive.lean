/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Coupling.Rank.Block

/-!
# Product law for adaptive rank splicing

The past-measurable rank choice preserves the target root-indexed product law.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

/-- A past-measurable equal-rank matching of generation-`n` populations
preserves the complete target product law.  Countability is localized to the
actual range of the random chosen family. -/
theorem RootIndexed.stepFieldLaw_spliceByRank
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (n : ℕ)
    (sourceValue targetValue :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (hsourceDepth : ∀ field p, p ∈ source field → p.2.length = n)
    (hcount : (Set.range
      (RootIndexed.rankChoice n sourceValue targetValue source target)).Countable)
    (hfiber : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field |
        RootIndexed.rankChoice n sourceValue targetValue source target field =
          roots}) :
    (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (RootIndexed.StepField.splice n
          (RootIndexed.rankChoice n sourceValue targetValue source target)) =
      RootIndexed.stepFieldLaw (Root := Root) μ := by
  exact RootIndexed.stepFieldLaw_splice μ n
    (RootIndexed.rankChoice n sourceValue targetValue source target)
    hcount hfiber
    (RootIndexed.rankChoice_depth n sourceValue targetValue source target
      hsourceDepth)
    (RootIndexed.rankChoice_injective n sourceValue targetValue source target)

end ProbabilityTheory.BranchingRandomWalk.Coupling

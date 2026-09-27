import Probability.BranchingRandomWalk.Selection.NSelection.Matching.Law
import Probability.BranchingRandomWalk.Selection.Coupling.Field.Adaptive

/-!
# Predictable equal-rank matching

This file instantiates predictable descendant-field pasting with the guarded
equal-rank inverse.  The selected source and target populations and their
ranking values may depend on the past of the joint source/fallback field.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

/-- At every target node of generation `n`, choose the source node of equal
rank when it exists and otherwise choose the same node in the fallback copy. -/
noncomputable def RootIndexed.rankChoice
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (sourceValue targetValue :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X)
    (q : RootIndexed.Generation Root α n) :
    (Root ⊕ Root) × TreeNode α :=
  RootIndexed.StepField.pasteCoordinate
    (preimageByRank (sourceValue field) (targetValue field)
      (source field) (target field)) q.1

/-- Every chosen root lies in generation `n` when the source population does. -/
theorem RootIndexed.rankChoice_depth
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (sourceValue targetValue :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (hsourceDepth : ∀ field p, p ∈ source field → p.2.length = n)
    (field : RootIndexed.StepField (Root ⊕ Root) α X)
    (q : RootIndexed.Generation Root α n) :
    (RootIndexed.rankChoice n sourceValue targetValue source target field q).2.length = n := by
  unfold RootIndexed.rankChoice RootIndexed.StepField.pasteCoordinate
  cases hpre : preimageByRank (sourceValue field) (targetValue field)
      (source field) (target field) q.1 with
  | none => exact q.2
  | some p =>
      exact hsourceDepth field p
        (preimageByRank_eq_some_iff.mp hpre).2.1

/-- The chosen family is injective for every sample. -/
theorem RootIndexed.rankChoice_injective
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (sourceValue targetValue :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    Function.Injective
      (RootIndexed.rankChoice n sourceValue targetValue source target field) := by
  intro q₁ q₂ hq
  apply Subtype.ext
  apply RootIndexed.StepField.pasteCoordinate_injective
    (preimageByRank (sourceValue field) (targetValue field)
      (source field) (target field))
    (fun r₁ r₂ p => preimageByRank_leftUnique
      (sourceValue field) (targetValue field)
      (source field) (target field))
  exact hq

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

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

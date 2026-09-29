import Probability.BranchingRandomWalk.Coupling.Rank.Field
import Probability.BranchingRandomWalk.Coupling.Field.Law

/-!
# Product law of a fixed rank matching

For fixed source and target populations, install the source coordinate of
each rank into the target coordinate of the same rank.  Source and fallback
are the two summands of one product field.  The installed target is again a
complete i.i.d. field.

This is a fixed-cell theorem.  Random, past-measurable populations are handled
later by partitioning over their actual range.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

/-- Fixed equal-rank installation is the generic paste operation associated
with the guarded inverse matching. -/
theorem RootIndexed.rankInstalledStepField_eq_paste
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue targetValue : RootIndexed.TreeNode Root α → Value)
    (source target : Finset (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.rankInstalledStepField
        (fun _ => sourceValue) (fun _ => targetValue)
        (fun _ => source) (fun _ => target)
        (fun sample r u => sample (Sum.inl r) u)
        (fun sample r u => sample (Sum.inr r) u) field =
      RootIndexed.StepField.paste
        (preimageByRank sourceValue targetValue source target) field := by
  funext r u
  simp only [RootIndexed.rankInstalledStepField, valueAtMatchedRank,
    Coupling.valueAtPreimage, RootIndexed.StepField.paste,
    RootIndexed.StepField.reindexCoordinates_apply]
  cases h : preimageByRank sourceValue targetValue source target (r, u) <;>
    simp [RootIndexed.StepField.pasteCoordinate, h]

/-- Installing a fixed equal-rank matching between two independent copies
preserves the root-indexed product law.  Roots and offspring slots may be
arbitrary types. -/
theorem RootIndexed.stepFieldLaw_rankInstalledStepField
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (sourceValue targetValue : RootIndexed.TreeNode Root α → Value)
    (source target : Finset (RootIndexed.TreeNode Root α)) :
    (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (fun field => RootIndexed.rankInstalledStepField
          (fun _ => sourceValue) (fun _ => targetValue)
          (fun _ => source) (fun _ => target)
          (fun sample r u => sample (Sum.inl r) u)
          (fun sample r u => sample (Sum.inr r) u) field) =
      RootIndexed.stepFieldLaw (Root := Root) μ := by
  rw [show (fun field => RootIndexed.rankInstalledStepField
      (fun _ => sourceValue) (fun _ => targetValue)
      (fun _ => source) (fun _ => target)
      (fun sample r u => sample (Sum.inl r) u)
      (fun sample r u => sample (Sum.inr r) u) field) =
      RootIndexed.StepField.paste
        (preimageByRank sourceValue targetValue source target) by
    funext field
    exact RootIndexed.rankInstalledStepField_eq_paste
      sourceValue targetValue source target field]
  exact RootIndexed.stepFieldLaw_paste μ
    (preimageByRank sourceValue targetValue source target)
    (fun q₁ q₂ p => preimageByRank_leftUnique
      sourceValue targetValue source target)

end ProbabilityTheory.BranchingRandomWalk.Coupling

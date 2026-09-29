import Probability.BranchingRandomWalk.Coupling.Field.Ranked
import Probability.BranchingRandomWalk.Coupling.Rank.Adaptive

/-!
# Recursive rank-matching primitives

Source and fallback copies, the fresh-coordinate map for one generation, and
its recursive successor identity.  These deterministic interfaces are shared
by the measurability and product-law layers.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

/-- The source (left) copy of a joint product field. -/
def RootIndexed.StepField.left
    {Root α X : Type*}
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.StepField Root α X :=
  field.reindex Sum.inl

/-- The fallback (right) copy of a joint product field. -/
def RootIndexed.StepField.right
    {Root α X : Type*}
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.StepField Root α X :=
  field.reindex Sum.inr

/-- The complete fresh-coordinate map used at one recursive matching stage. -/
noncomputable def RootIndexed.rankInstalledBlockChoice
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        Finset (RootIndexed.TreeNode Root α))
    (n : ℕ) :
    RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.Generation Root α n × TreeNode α →
        (Root ⊕ Root) × TreeNode α :=
  let prior := RootIndexed.rankInstalledField sourceValue targetValue source target
    RootIndexed.StepField.left RootIndexed.StepField.right n
  RootIndexed.rankBlockChoice n
    (sourceValue n) (fun field => targetValue n field (prior field))
    (source n) (fun field => target n field (prior field))

/-- One recursive successor stage is the predictable coordinate gluing used
by the product-law theorem. -/
theorem RootIndexed.rankInstalledField_succ_eq_glue
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        Finset (RootIndexed.TreeNode Root α))
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.rankInstalledField sourceValue targetValue source target
        RootIndexed.StepField.left RootIndexed.StepField.right (n + 1) field =
      let prior := RootIndexed.rankInstalledField sourceValue targetValue source target
        RootIndexed.StepField.left RootIndexed.StepField.right n field
      RootIndexed.StepField.glue n (prior.past n)
        (RootIndexed.selectedCoordinateField
          (RootIndexed.rankInstalledBlockChoice sourceValue targetValue source target n)
          field) := by
  let prior := RootIndexed.rankInstalledField sourceValue targetValue source target
    RootIndexed.StepField.left RootIndexed.StepField.right n field
  rw [RootIndexed.rankInstalledField_succ]
  symm
  apply RootIndexed.glue_rankBlockChoice_eq_updateGeneration
  intro r u hu
  exact RootIndexed.rankInstalledField_apply_of_le_length sourceValue targetValue
    source target RootIndexed.StepField.left RootIndexed.StepField.right
    n field r u hu

end ProbabilityTheory.BranchingRandomWalk.Coupling

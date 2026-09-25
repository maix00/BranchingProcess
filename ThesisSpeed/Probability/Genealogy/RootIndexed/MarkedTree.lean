import ThesisSpeed.Probability.Genealogy.BranchingPositions
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

/-! Marked branching trees indexed by an arbitrary type of initial roots. -/

abbrev RootIndexedMarkedTree (Root : Type*) (X : Type*) [AddCommMonoid X] :=
  Root → BranchingMarkedTree X

def RootIndexedMarkedTree.ofStep {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) : RootIndexedMarkedTree Root X :=
  fun i => BranchingMarkedTree.ofStep (step i)

@[simp] theorem RootIndexedMarkedTree.ofStep_apply
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) :
    RootIndexedMarkedTree.ofStep step i =
      BranchingMarkedTree.ofStep (step i) := rfl

theorem RootIndexedMarkedTree.ofStep_mark
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) (u : TreeNode) :
    (RootIndexedMarkedTree.ofStep step i).mark u =
      branchingTreePathSum (step i) u := by
  exact congrFun (BranchingMarkedTree.ofStep_mark (step i)) u

def rootIndexedNodePosition {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) (u : TreeNode) : X :=
  branchingTreePathSum (step i) u

theorem rootIndexedNodePosition_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : TreeNode) :
    rootIndexedNodePosition (step.reindex f) i u =
      rootIndexedNodePosition step (f i) u := by
  rfl

@[simp] theorem rootIndexedNodePosition_nil
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) :
    rootIndexedNodePosition step i [] = 0 := by
  exact branchingTreePathSum_nil (step i)

theorem rootIndexedNodePosition_append_singleton
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) (u : TreeNode) (j : ℕ) :
    rootIndexedNodePosition step i (u ++ [j]) =
      rootIndexedNodePosition step i u +
        branchingStepIncrement (step i u) j := by
  exact branchingTreePathSum_append_singleton (step i) u j

def rootIndexedAbsolutePosition {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : TreeNode) : X :=
  initial i + rootIndexedNodePosition step i u

theorem rootIndexedAbsolutePosition_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : TreeNode) :
    rootIndexedAbsolutePosition (initial ∘ f) (step.reindex f) i u =
      rootIndexedAbsolutePosition initial step (f i) u := by
  rfl

theorem rootIndexedAbsolutePosition_eq_initial_add_mark
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : TreeNode) :
    rootIndexedAbsolutePosition initial step i u =
      initial i + (RootIndexedMarkedTree.ofStep step i).mark u := by
  simp [rootIndexedAbsolutePosition, rootIndexedNodePosition]

@[simp] theorem rootIndexedAbsolutePosition_root
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X) (i : Root) :
    rootIndexedAbsolutePosition initial step i [] = initial i := by
  simp [rootIndexedAbsolutePosition]

theorem rootIndexedAbsolutePosition_append_singleton
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : TreeNode) (j : ℕ) :
    rootIndexedAbsolutePosition initial step i (u ++ [j]) =
      rootIndexedAbsolutePosition initial step i u +
        branchingStepIncrement (step i u) j := by
  simp only [rootIndexedAbsolutePosition,
    rootIndexedNodePosition_append_singleton, add_assoc]

theorem rootIndexedAbsolutePosition_append_two
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : TreeNode) (j k : ℕ) :
    rootIndexedAbsolutePosition initial step i (u ++ [j, k]) =
      rootIndexedAbsolutePosition initial step i u +
        branchingStepIncrement (step i u) j +
        branchingStepIncrement (step i (u ++ [j])) k := by
  unfold rootIndexedAbsolutePosition rootIndexedNodePosition
  rw [branchingTreePathSum_append_two]
  simp only [add_assoc]

theorem rootIndexedNodePosition_append
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root)
    (u v : TreeNode) :
    rootIndexedNodePosition step i (u ++ v) =
      rootIndexedNodePosition step i u +
        branchingTreePathSum (fun w => step i (u ++ w)) v := by
  exact branchingTreePathSum_append (step i) u v

theorem rootIndexedAbsolutePosition_append
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u v : TreeNode) :
    rootIndexedAbsolutePosition initial step i (u ++ v) =
      rootIndexedAbsolutePosition initial step i u +
        branchingTreePathSum (fun w => step i (u ++ w)) v := by
  unfold rootIndexedAbsolutePosition
  rw [rootIndexedNodePosition_append]
  simp only [add_assoc]

def rootIndexedRealizedNode {Root : Type*} {X : Type*}
    (step : RootIndexedBranchingStepField Root X) (i : Root) (u : TreeNode) : Prop :=
  branchingRealizedNode (step i) u

theorem rootIndexedRealizedNode_reindex
    {Root NewRoot : Type*} {X : Type*}
    (step : RootIndexedBranchingStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : TreeNode) :
    rootIndexedRealizedNode (step.reindex f) i u ↔
      rootIndexedRealizedNode step (f i) u := by
  rfl

@[simp] theorem rootIndexedRealizedNode_nil
    {Root : Type*} {X : Type*} (step : RootIndexedBranchingStepField Root X) (i : Root) :
    rootIndexedRealizedNode step i [] := by
  exact branchingRealizedNode_nil (step i)

theorem rootIndexedRealizedNode_append_iff
    {Root : Type*} {X : Type*} (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u v : TreeNode) :
    rootIndexedRealizedNode step i (u ++ v) ↔
      rootIndexedRealizedNode step i u ∧
        branchingRealizedNode (fun w => step i (u ++ w)) v := by
  exact branchingRealizedNode_append_iff (step i) u v

end ThesisSpeed

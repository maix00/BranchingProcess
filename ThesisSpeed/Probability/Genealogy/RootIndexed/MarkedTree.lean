import ThesisSpeed.Probability.Genealogy.BranchingPositions
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

/-! Marked branching trees indexed by an arbitrary type of initial roots. -/

def rootIndexedNodeDisplacement {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) (u : TreeNode) : X :=
  branchingTreePathSum (step i) u

noncomputable def rootIndexedNodeDisplacement? {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) (u : TreeNode) : Option X :=
  branchingTreePathSum? (step i) u

theorem rootIndexedNodeDisplacement?_eq_some_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) (u : TreeNode) :
    rootIndexedNodeDisplacement? step i u =
        some (rootIndexedNodeDisplacement step i u) ↔
      branchingRealizedNode (step i) u := by
  exact branchingTreePathSum?_eq_some_iff (step i) u

theorem rootIndexedNodeDisplacement_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : TreeNode) :
    rootIndexedNodeDisplacement (step.reindex f) i u =
      rootIndexedNodeDisplacement step (f i) u := by
  rfl

@[simp] theorem rootIndexedNodeDisplacement_nil
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) :
    rootIndexedNodeDisplacement step i [] = 0 := by
  exact branchingTreePathSum_nil (step i)

theorem rootIndexedNodeDisplacement_append_singleton
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) (u : TreeNode) (j : ℕ) :
    rootIndexedNodeDisplacement step i (u ++ [j]) =
      rootIndexedNodeDisplacement step i u +
        branchingStepIncrement (step i u) j := by
  exact branchingTreePathSum_append_singleton (step i) u j

def rootIndexedNodePosition {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : TreeNode) : X :=
  initial i + rootIndexedNodeDisplacement step i u

theorem rootIndexedNodePosition_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : TreeNode) :
    rootIndexedNodePosition (initial ∘ f) (step.reindex f) i u =
      rootIndexedNodePosition initial step (f i) u := by
  rfl

theorem rootIndexedNodePosition_eq_initial_add_mark
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : TreeNode) :
    rootIndexedNodePosition initial step i u =
      initial i + branchingTreePathSum (step i) u := by
  simp [rootIndexedNodePosition, rootIndexedNodeDisplacement]

@[simp] theorem rootIndexedNodePosition_root
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X) (i : Root) :
    rootIndexedNodePosition initial step i [] = initial i := by
  simp [rootIndexedNodePosition]

theorem rootIndexedNodePosition_append_singleton
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : TreeNode) (j : ℕ) :
    rootIndexedNodePosition initial step i (u ++ [j]) =
      rootIndexedNodePosition initial step i u +
        branchingStepIncrement (step i u) j := by
  simp only [rootIndexedNodePosition,
    rootIndexedNodeDisplacement_append_singleton, add_assoc]

theorem rootIndexedNodePosition_append_two
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : TreeNode) (j k : ℕ) :
    rootIndexedNodePosition initial step i (u ++ [j, k]) =
      rootIndexedNodePosition initial step i u +
        branchingStepIncrement (step i u) j +
        branchingStepIncrement (step i (u ++ [j])) k := by
  unfold rootIndexedNodePosition rootIndexedNodeDisplacement
  rw [branchingTreePathSum_append_two]
  simp only [add_assoc]

theorem rootIndexedNodeDisplacement_append
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root)
    (u v : TreeNode) :
    rootIndexedNodeDisplacement step i (u ++ v) =
      rootIndexedNodeDisplacement step i u +
        branchingTreePathSum (fun w => step i (u ++ w)) v := by
  exact branchingTreePathSum_append (step i) u v

theorem rootIndexedNodePosition_append
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u v : TreeNode) :
    rootIndexedNodePosition initial step i (u ++ v) =
      rootIndexedNodePosition initial step i u +
        branchingTreePathSum (fun w => step i (u ++ w)) v := by
  unfold rootIndexedNodePosition
  rw [rootIndexedNodeDisplacement_append]
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

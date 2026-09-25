import ThesisSpeed.Probability.Genealogy.RootIndexed.Field
import ThesisSpeed.Probability.Genealogy.Position.Measurability
import ThesisSpeed.Probability.Genealogy.BranchingStep.PartialMark
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

/-! Root-indexed branching step fields and their accumulated positions.
    An arbitrary type indexes the initial roots; the accumulated mark and the
    initial-position-shifted position are defined per root. -/

def rootIndexedBranchingStepAccumulatedMark {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) (u : 𝕍) : X :=
  branchingStepAccumulatedMark (step i) u

def rootIndexedBranchingStepAccumulatedMark? {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) (u : 𝕍) : Option X :=
  branchingStepAccumulatedMark? (step i) u

theorem rootIndexedBranchingStepAccumulatedMark?_eq_some_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) (u : 𝕍) :
    rootIndexedBranchingStepAccumulatedMark? step i u =
        some (rootIndexedBranchingStepAccumulatedMark step i u) ↔
      branchingRealizedNode (step i) u := by
  rw [rootIndexedBranchingStepAccumulatedMark?, rootIndexedBranchingStepAccumulatedMark,
    branchingStepAccumulatedMark?_eq_some_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

theorem rootIndexedBranchingStepAccumulatedMark?_eq_none_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) (u : 𝕍) :
    rootIndexedBranchingStepAccumulatedMark? step i u = none ↔
      ¬ branchingRealizedNode (step i) u :=
  branchingStepAccumulatedMark?_eq_none_iff (step i) u

theorem rootIndexedBranchingStepAccumulatedMark_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : 𝕍) :
    rootIndexedBranchingStepAccumulatedMark (step.reindex f) i u =
      rootIndexedBranchingStepAccumulatedMark step (f i) u := by
  rfl

@[simp] theorem rootIndexedBranchingStepAccumulatedMark_nil
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) :
    rootIndexedBranchingStepAccumulatedMark step i [] = 0 := by
  exact branchingStepAccumulatedMark_nil (step i)

theorem rootIndexedBranchingStepAccumulatedMark_append_singleton
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) (u : 𝕍) (j : ℕ) :
    rootIndexedBranchingStepAccumulatedMark step i (u ++ [j]) =
      rootIndexedBranchingStepAccumulatedMark step i u +
        branchingStepIncrement (step i u) j := by
  exact branchingStepAccumulatedMark_append_singleton (step i) u j

def rootIndexedBranchingStepPosition {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : 𝕍) : X :=
  initial i + rootIndexedBranchingStepAccumulatedMark step i u

def rootIndexedBranchingStepPosition? {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : 𝕍) : Option X :=
  (rootIndexedBranchingStepAccumulatedMark? step i u).map (initial i + ·)

theorem rootIndexedBranchingStepAccumulatedMark?_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : 𝕍) :
    rootIndexedBranchingStepAccumulatedMark? (step.reindex f) i u =
      rootIndexedBranchingStepAccumulatedMark? step (f i) u := by
  rfl

theorem rootIndexedBranchingStepPosition?_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : 𝕍) :
    rootIndexedBranchingStepPosition? (initial ∘ f) (step.reindex f) i u =
      rootIndexedBranchingStepPosition? initial step (f i) u := by
  rfl

theorem rootIndexedBranchingStepPosition?_eq_some_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : 𝕍) :
    rootIndexedBranchingStepPosition? initial step i u =
        some (rootIndexedBranchingStepPosition initial step i u) ↔
      branchingRealizedNode (step i) u := by
  by_cases h : branchingRealizedNode (step i) u
  · have hsome := (rootIndexedBranchingStepAccumulatedMark?_eq_some_iff step i u).mpr h
    simp [rootIndexedBranchingStepPosition?, rootIndexedBranchingStepPosition, hsome]
    exact h
  · have hnone := (rootIndexedBranchingStepAccumulatedMark?_eq_none_iff step i u).mpr h
    simp [rootIndexedBranchingStepPosition?, hnone]
    exact h

theorem rootIndexedBranchingStepPosition?_eq_none_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : 𝕍) :
    rootIndexedBranchingStepPosition? initial step i u = none ↔
      ¬ branchingRealizedNode (step i) u := by
  by_cases h : branchingRealizedNode (step i) u
  · have hsome := (rootIndexedBranchingStepAccumulatedMark?_eq_some_iff step i u).mpr h
    simp [rootIndexedBranchingStepPosition?, hsome]
    exact h
  · have hnone := (rootIndexedBranchingStepAccumulatedMark?_eq_none_iff step i u).mpr h
    simp [rootIndexedBranchingStepPosition?, hnone]
    exact h

theorem rootIndexedBranchingStepPosition_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : 𝕍) :
    rootIndexedBranchingStepPosition (initial ∘ f) (step.reindex f) i u =
      rootIndexedBranchingStepPosition initial step (f i) u := by
  rfl

theorem rootIndexedBranchingStepPosition_eq_initial_add_mark
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : 𝕍) :
    rootIndexedBranchingStepPosition initial step i u =
      initial i + branchingStepAccumulatedMark (step i) u := by
  simp [rootIndexedBranchingStepPosition, rootIndexedBranchingStepAccumulatedMark]

@[simp] theorem rootIndexedBranchingStepPosition_root
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X) (i : Root) :
    rootIndexedBranchingStepPosition initial step i [] = initial i := by
  simp [rootIndexedBranchingStepPosition]

theorem rootIndexedBranchingStepPosition_append_singleton
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : 𝕍) (j : ℕ) :
    rootIndexedBranchingStepPosition initial step i (u ++ [j]) =
      rootIndexedBranchingStepPosition initial step i u +
        branchingStepIncrement (step i u) j := by
  simp only [rootIndexedBranchingStepPosition,
    rootIndexedBranchingStepAccumulatedMark_append_singleton, add_assoc]

theorem rootIndexedBranchingStepPosition_append_two
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : 𝕍) (j k : ℕ) :
    rootIndexedBranchingStepPosition initial step i (u ++ [j, k]) =
      rootIndexedBranchingStepPosition initial step i u +
        branchingStepIncrement (step i u) j +
        branchingStepIncrement (step i (u ++ [j])) k := by
  unfold rootIndexedBranchingStepPosition rootIndexedBranchingStepAccumulatedMark
  rw [branchingStepAccumulatedMark_append_two]
  simp only [add_assoc]

theorem rootIndexedBranchingStepAccumulatedMark_append
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root)
    (u v : 𝕍) :
    rootIndexedBranchingStepAccumulatedMark step i (u ++ v) =
      rootIndexedBranchingStepAccumulatedMark step i u +
        branchingStepAccumulatedMark (fun w => step i (u ++ w)) v := by
  exact branchingStepAccumulatedMark_append (step i) u v

theorem rootIndexedBranchingStepPosition_append
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u v : 𝕍) :
    rootIndexedBranchingStepPosition initial step i (u ++ v) =
      rootIndexedBranchingStepPosition initial step i u +
        branchingStepAccumulatedMark (fun w => step i (u ++ w)) v := by
  unfold rootIndexedBranchingStepPosition
  rw [rootIndexedBranchingStepAccumulatedMark_append]
  simp only [add_assoc]

def rootIndexedRealizedNode {Root : Type*} {X : Type*}
    (step : RootIndexedBranchingStepField Root X) (i : Root) (u : 𝕍) : Prop :=
  branchingRealizedNode (step i) u

theorem rootIndexedRealizedNode_reindex
    {Root NewRoot : Type*} {X : Type*}
    (step : RootIndexedBranchingStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : 𝕍) :
    rootIndexedRealizedNode (step.reindex f) i u ↔
      rootIndexedRealizedNode step (f i) u := by
  rfl

@[simp] theorem rootIndexedRealizedNode_nil
    {Root : Type*} {X : Type*} (step : RootIndexedBranchingStepField Root X) (i : Root) :
    rootIndexedRealizedNode step i [] := by
  exact branchingRealizedNode_nil (step i)

theorem rootIndexedRealizedNode_append_iff
    {Root : Type*} {X : Type*} (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u v : 𝕍) :
    rootIndexedRealizedNode step i (u ++ v) ↔
      rootIndexedRealizedNode step i u ∧
        branchingRealizedNode (fun w => step i (u ++ w)) v := by
  exact branchingRealizedNode_append_iff (step i) u v

end ThesisSpeed

import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field
import Combinatorics.BranchingStep.Position.Increment
import Probability.BranchingRandomWalk.Step.Position.Measurability
import Combinatorics.BranchingStep.Position.Partial
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



/-! Root-indexed branching step fields and their accumulated positions.
    An arbitrary type indexes the initial roots; the accumulated mark and the
    initial-position-shifted position are defined per root. -/

def rootIndexedAccumulate {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) (u : 𝕍) : X :=
  accumulateRoot (step i) u

def rootIndexedAccumulate? {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) (u : 𝕍) : Option X :=
  accumulateRoot? (step i) u

theorem rootIndexedAccumulate?_eq_some_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) (u : 𝕍) :
    rootIndexedAccumulate? step i u =
        some (rootIndexedAccumulate step i u) ↔
      realizedNode (step i) u := by
  rw [rootIndexedAccumulate?, rootIndexedAccumulate,
    accumulateRoot?_eq_some_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

theorem rootIndexedAccumulate?_eq_none_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) (u : 𝕍) :
    rootIndexedAccumulate? step i u = none ↔
      ¬ realizedNode (step i) u :=
  accumulateRoot?_eq_none_iff (step i) u

theorem rootIndexedAccumulate_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : 𝕍) :
    rootIndexedAccumulate (step.reindex f) i u =
      rootIndexedAccumulate step (f i) u := by
  rfl

@[simp] theorem rootIndexedAccumulate_nil
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) :
    rootIndexedAccumulate step i [] = 0 := by
  exact accumulateRoot_nil (step i)

theorem rootIndexedAccumulate_append_singleton
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) (u : 𝕍) (j : ℕ) :
    rootIndexedAccumulate step i (u ++ [j]) =
      rootIndexedAccumulate step i u +
        BranchingStep.step (step i u) j := by
  exact accumulateRoot_append_singleton (step i) u j

def rootIndexedStepPosition {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) : X :=
  initial i + rootIndexedAccumulate step i u

def rootIndexedStepPosition? {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) : Option X :=
  (rootIndexedAccumulate? step i u).map (initial i + ·)

theorem rootIndexedAccumulate?_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : 𝕍) :
    rootIndexedAccumulate? (step.reindex f) i u =
      rootIndexedAccumulate? step (f i) u := by
  rfl

theorem rootIndexedStepPosition?_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : 𝕍) :
    rootIndexedStepPosition? (initial ∘ f) (step.reindex f) i u =
      rootIndexedStepPosition? initial step (f i) u := by
  rfl

theorem rootIndexedStepPosition?_eq_some_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) :
    rootIndexedStepPosition? initial step i u =
        some (rootIndexedStepPosition initial step i u) ↔
      realizedNode (step i) u := by
  by_cases h : realizedNode (step i) u
  · have hsome := (rootIndexedAccumulate?_eq_some_iff step i u).mpr h
    simp [rootIndexedStepPosition?, rootIndexedStepPosition, hsome]
    exact h
  · have hnone := (rootIndexedAccumulate?_eq_none_iff step i u).mpr h
    simp [rootIndexedStepPosition?, hnone]
    exact h

theorem rootIndexedStepPosition?_eq_none_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) :
    rootIndexedStepPosition? initial step i u = none ↔
      ¬ realizedNode (step i) u := by
  by_cases h : realizedNode (step i) u
  · have hsome := (rootIndexedAccumulate?_eq_some_iff step i u).mpr h
    simp [rootIndexedStepPosition?, hsome]
    exact h
  · have hnone := (rootIndexedAccumulate?_eq_none_iff step i u).mpr h
    simp [rootIndexedStepPosition?, hnone]
    exact h

theorem rootIndexedStepPosition_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : 𝕍) :
    rootIndexedStepPosition (initial ∘ f) (step.reindex f) i u =
      rootIndexedStepPosition initial step (f i) u := by
  rfl

theorem rootIndexedStepPosition_eq_initial_add_mark
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) :
    rootIndexedStepPosition initial step i u =
      initial i + accumulateRoot (step i) u := by
  simp [rootIndexedStepPosition, rootIndexedAccumulate]

@[simp] theorem rootIndexedStepPosition_root
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X) (i : Root) :
    rootIndexedStepPosition initial step i [] = initial i := by
  simp [rootIndexedStepPosition]

theorem rootIndexedStepPosition_append_singleton
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) (j : ℕ) :
    rootIndexedStepPosition initial step i (u ++ [j]) =
      rootIndexedStepPosition initial step i u +
        BranchingStep.step (step i u) j := by
  simp only [rootIndexedStepPosition,
    rootIndexedAccumulate_append_singleton, add_assoc]

theorem rootIndexedStepPosition_append_two
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) (j k : ℕ) :
    rootIndexedStepPosition initial step i (u ++ [j, k]) =
      rootIndexedStepPosition initial step i u +
        BranchingStep.step (step i u) j +
        BranchingStep.step (step i (u ++ [j])) k := by
  unfold rootIndexedStepPosition rootIndexedAccumulate
  rw [accumulateRoot_append_two]
  simp only [add_assoc]

theorem rootIndexedAccumulate_append
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root)
    (u v : 𝕍) :
    rootIndexedAccumulate step i (u ++ v) =
      rootIndexedAccumulate step i u +
        accumulateRoot (fun w => step i (u ++ w)) v := by
  exact accumulateRoot_append (step i) u v

theorem rootIndexedStepPosition_append
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u v : 𝕍) :
    rootIndexedStepPosition initial step i (u ++ v) =
      rootIndexedStepPosition initial step i u +
        accumulateRoot (fun w => step i (u ++ w)) v := by
  unfold rootIndexedStepPosition
  rw [rootIndexedAccumulate_append]
  simp only [add_assoc]

def rootIndexedRealizedNode {Root : Type*} {X : Type*}
    (step : RootIndexedStepField Root X) (i : Root) (u : 𝕍) : Prop :=
  realizedNode (step i) u

theorem rootIndexedRealizedNode_reindex
    {Root NewRoot : Type*} {X : Type*}
    (step : RootIndexedStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : 𝕍) :
    rootIndexedRealizedNode (step.reindex f) i u ↔
      rootIndexedRealizedNode step (f i) u := by
  rfl

@[simp] theorem rootIndexedRealizedNode_nil
    {Root : Type*} {X : Type*} (step : RootIndexedStepField Root X) (i : Root) :
    rootIndexedRealizedNode step i [] := by
  exact realizedNode_nil (step i)

theorem rootIndexedRealizedNode_append_iff
    {Root : Type*} {X : Type*} (step : RootIndexedStepField Root X)
    (i : Root) (u v : 𝕍) :
    rootIndexedRealizedNode step i (u ++ v) ↔
      rootIndexedRealizedNode step i u ∧
        realizedNode (fun w => step i (u ++ w)) v := by
  exact realizedNode_append_iff (step i) u v

end ProbabilityTheory.BranchingRandomWalk

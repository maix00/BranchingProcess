import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field
import MeasureTheory.BranchingWalk.Position.Increment
import Probability.BranchingRandomWalk.Step.Position.Measurability
import MeasureTheory.BranchingWalk.Position.Partial
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory



/-! Root-indexed branching step fields and their positions.
    An arbitrary type indexes the initial roots; the displacement and the
    initial-position-shifted position are defined per root. -/

def rootIndexedDisplace {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) (u : 𝕍) : X :=
  displaceRoot (step i) u

def rootIndexedDisplace? {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) (u : 𝕍) : Option X :=
  displaceRoot? (step i) u

theorem rootIndexedDisplace?_eq_some_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) (u : 𝕍) :
    rootIndexedDisplace? step i u =
        some (rootIndexedDisplace step i u) ↔
      realizedNode (step i) u := by
  rw [rootIndexedDisplace?, rootIndexedDisplace,
    displaceRoot?_eq_some_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

theorem rootIndexedDisplace?_eq_none_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) (u : 𝕍) :
    rootIndexedDisplace? step i u = none ↔
      ¬ realizedNode (step i) u :=
  displaceRoot?_eq_none_iff (step i) u

theorem rootIndexedDisplace_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : 𝕍) :
    rootIndexedDisplace (step.reindex f) i u =
      rootIndexedDisplace step (f i) u := by
  rfl

@[simp] theorem rootIndexedDisplace_nil
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) :
    rootIndexedDisplace step i [] = 0 := by
  exact displaceRoot_nil (step i)

theorem rootIndexedDisplace_append_singleton
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) (u : 𝕍) (j : ℕ) :
    rootIndexedDisplace step i (u ++ [j]) =
      rootIndexedDisplace step i u +
        MeasureTheory.BranchingWalk.value (step i u) j := by
  exact displaceRoot_append_singleton (step i) u j

def rootIndexedStepPosition {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) : X :=
  initial i + rootIndexedDisplace step i u

def rootIndexedStepPosition? {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) : Option X :=
  (rootIndexedDisplace? step i u).map (initial i + ·)

theorem rootIndexedDisplace?_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : 𝕍) :
    rootIndexedDisplace? (step.reindex f) i u =
      rootIndexedDisplace? step (f i) u := by
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
  · have hsome := (rootIndexedDisplace?_eq_some_iff step i u).mpr h
    simp [rootIndexedStepPosition?, rootIndexedStepPosition, hsome]
    exact h
  · have hnone := (rootIndexedDisplace?_eq_none_iff step i u).mpr h
    simp [rootIndexedStepPosition?, hnone]
    exact h

theorem rootIndexedStepPosition?_eq_none_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) :
    rootIndexedStepPosition? initial step i u = none ↔
      ¬ realizedNode (step i) u := by
  by_cases h : realizedNode (step i) u
  · have hsome := (rootIndexedDisplace?_eq_some_iff step i u).mpr h
    simp [rootIndexedStepPosition?, hsome]
    exact h
  · have hnone := (rootIndexedDisplace?_eq_none_iff step i u).mpr h
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
      initial i + displaceRoot (step i) u := by
  simp [rootIndexedStepPosition, rootIndexedDisplace]

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
        MeasureTheory.BranchingWalk.value (step i u) j := by
  simp only [rootIndexedStepPosition,
    rootIndexedDisplace_append_singleton, add_assoc]

theorem rootIndexedStepPosition_append_two
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) (j k : ℕ) :
    rootIndexedStepPosition initial step i (u ++ [j, k]) =
      rootIndexedStepPosition initial step i u +
        MeasureTheory.BranchingWalk.value (step i u) j +
        MeasureTheory.BranchingWalk.value (step i (u ++ [j])) k := by
  unfold rootIndexedStepPosition rootIndexedDisplace
  rw [displaceRoot_append_two]
  simp only [add_assoc]

theorem rootIndexedDisplace_append
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root)
    (u v : 𝕍) :
    rootIndexedDisplace step i (u ++ v) =
      rootIndexedDisplace step i u +
        displaceRoot (fun w => step i (u ++ w)) v := by
  exact displaceRoot_append (step i) u v

theorem rootIndexedStepPosition_append
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u v : 𝕍) :
    rootIndexedStepPosition initial step i (u ++ v) =
      rootIndexedStepPosition initial step i u +
        displaceRoot (fun w => step i (u ++ w)) v := by
  unfold rootIndexedStepPosition
  rw [rootIndexedDisplace_append]
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

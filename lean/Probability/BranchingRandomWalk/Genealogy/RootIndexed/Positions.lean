import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field
import Combinatorics.BranchingWalk.Step.Basic
import Probability.BranchingRandomWalk.Step.Position.Measurability
import Combinatorics.BranchingWalk.Basic.Displace
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



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
      surviveAlong (step i) [] u := by
  rw [rootIndexedDisplace?, rootIndexedDisplace,
    displaceRoot?_eq_some_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

theorem rootIndexedDisplace?_eq_none_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) (u : 𝕍) :
    rootIndexedDisplace? step i u = none ↔
      ¬ surviveAlong (step i) [] u :=
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
        Combinatorics.Branching.value' (step i u) j := by
  exact displaceRoot_append_singleton (step i) u j

def rootIndexedPosition {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) : X :=
  initial i + rootIndexedDisplace step i u

def rootIndexedPosition? {Root : Type*} {X : Type*} [AddCommMonoid X]
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

theorem rootIndexedPosition?_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : 𝕍) :
    rootIndexedPosition? (initial ∘ f) (step.reindex f) i u =
      rootIndexedPosition? initial step (f i) u := by
  rfl

theorem rootIndexedPosition?_eq_some_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) :
    rootIndexedPosition? initial step i u =
        some (rootIndexedPosition initial step i u) ↔
      surviveAlong (step i) [] u := by
  by_cases h : surviveAlong (step i) [] u
  · have hsome := (rootIndexedDisplace?_eq_some_iff step i u).mpr h
    simp [rootIndexedPosition?, rootIndexedPosition, hsome]
    exact h
  · have hnone := (rootIndexedDisplace?_eq_none_iff step i u).mpr h
    simp [rootIndexedPosition?, hnone]
    exact h

theorem rootIndexedPosition?_eq_none_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) :
    rootIndexedPosition? initial step i u = none ↔
      ¬ surviveAlong (step i) [] u := by
  by_cases h : surviveAlong (step i) [] u
  · have hsome := (rootIndexedDisplace?_eq_some_iff step i u).mpr h
    simp [rootIndexedPosition?, hsome]
    exact h
  · have hnone := (rootIndexedDisplace?_eq_none_iff step i u).mpr h
    simp [rootIndexedPosition?, hnone]
    exact h

theorem rootIndexedPosition_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : 𝕍) :
    rootIndexedPosition (initial ∘ f) (step.reindex f) i u =
      rootIndexedPosition initial step (f i) u := by
  rfl

theorem rootIndexedPosition_eq_initial_add_mark
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) :
    rootIndexedPosition initial step i u =
      initial i + displaceRoot (step i) u := by
  simp [rootIndexedPosition, rootIndexedDisplace]

@[simp] theorem rootIndexedPosition_root
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X) (i : Root) :
    rootIndexedPosition initial step i [] = initial i := by
  simp [rootIndexedPosition]

theorem rootIndexedPosition_append_singleton
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) (j : ℕ) :
    rootIndexedPosition initial step i (u ++ [j]) =
      rootIndexedPosition initial step i u +
        Combinatorics.Branching.value' (step i u) j := by
  simp only [rootIndexedPosition,
    rootIndexedDisplace_append_singleton, add_assoc]

theorem rootIndexedPosition_append_two
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) (j k : ℕ) :
    rootIndexedPosition initial step i (u ++ [j, k]) =
      rootIndexedPosition initial step i u +
        Combinatorics.Branching.value' (step i u) j +
        Combinatorics.Branching.value' (step i (u ++ [j])) k := by
  unfold rootIndexedPosition rootIndexedDisplace
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

theorem rootIndexedPosition_append
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u v : 𝕍) :
    rootIndexedPosition initial step i (u ++ v) =
      rootIndexedPosition initial step i u +
        displaceRoot (fun w => step i (u ++ w)) v := by
  unfold rootIndexedPosition
  rw [rootIndexedDisplace_append]
  simp only [add_assoc]

def rootIndexedRealizedNode {Root : Type*} {X : Type*}
    (step : RootIndexedStepField Root X) (i : Root) (u : 𝕍) : Prop :=
  surviveAlong (step i) [] u

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
  exact surviveAlong_nil (step i) []

theorem rootIndexedRealizedNode_append_iff
    {Root : Type*} {X : Type*} (step : RootIndexedStepField Root X)
    (i : Root) (u v : 𝕍) :
    rootIndexedRealizedNode step i (u ++ v) ↔
      rootIndexedRealizedNode step i u ∧
        surviveAlong (step i) u v := by
  exact surviveAlong_append (step i) [] u v

end ProbabilityTheory.BranchingRandomWalk

import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field
import Combinatorics.BranchingWalk.Step.Basic
import Probability.BranchingRandomWalk.Step.Position.Measurability
import Combinatorics.BranchingWalk.Basic.Displace
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

namespace RootIndexed

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



/-! Root-indexed branching step fields and their positions.
    An arbitrary type indexes the initial roots; the displacement and the
    initial-position-shifted position are defined per root. -/

def displace {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) (u : 𝕍) : X :=
  displaceRoot (step i) u

def displace? {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) (u : 𝕍) : Option X :=
  displaceRoot? (step i) u

theorem displace?_eq_some_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) (u : 𝕍) :
    displace? step i u =
        some (displace step i u) ↔
      surviveAlong (step i) [] u := by
  rw [displace?, displace,
    displaceRoot?_eq_some_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

theorem displace?_eq_none_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) (u : 𝕍) :
    displace? step i u = none ↔
      ¬ surviveAlong (step i) [] u :=
  displaceRoot?_eq_none_iff (step i) u

theorem displace_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : 𝕍) :
    displace (step.reindex f) i u =
      displace step (f i) u := by
  rfl

@[simp] theorem displace_nil
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) :
    displace step i [] = 0 := by
  exact displaceRoot_nil (step i)

theorem displace_append_singleton
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root) (u : 𝕍) (j : ℕ) :
    displace step i (u ++ [j]) =
      displace step i u +
        Combinatorics.Branching.value' (step i u) j := by
  exact displaceRoot_append_singleton (step i) u j

def position {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) : X :=
  initial i + displace step i u

def position? {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) : Option X :=
  (displace? step i u).map (initial i + ·)

theorem displace?_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : 𝕍) :
    displace? (step.reindex f) i u =
      displace? step (f i) u := by
  rfl

theorem position?_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : 𝕍) :
    position? (initial ∘ f) (step.reindex f) i u =
      position? initial step (f i) u := by
  rfl

theorem position?_eq_some_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) :
    position? initial step i u =
        some (position initial step i u) ↔
      surviveAlong (step i) [] u := by
  by_cases h : surviveAlong (step i) [] u
  · have hsome := (displace?_eq_some_iff step i u).mpr h
    simp [position?, position, hsome]
    exact h
  · have hnone := (displace?_eq_none_iff step i u).mpr h
    simp [position?, hnone]
    exact h

theorem position?_eq_none_iff
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) :
    position? initial step i u = none ↔
      ¬ surviveAlong (step i) [] u := by
  by_cases h : surviveAlong (step i) [] u
  · have hsome := (displace?_eq_some_iff step i u).mpr h
    simp [position?, hsome]
    exact h
  · have hnone := (displace?_eq_none_iff step i u).mpr h
    simp [position?, hnone]
    exact h

theorem position_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : 𝕍) :
    position (initial ∘ f) (step.reindex f) i u =
      position initial step (f i) u := by
  rfl

theorem position_eq_initial_add_mark
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) :
    position initial step i u =
      initial i + displaceRoot (step i) u := by
  simp [position, displace]

@[simp] theorem position_root
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X) (i : Root) :
    position initial step i [] = initial i := by
  simp [position]

theorem position_append_singleton
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) (j : ℕ) :
    position initial step i (u ++ [j]) =
      position initial step i u +
        Combinatorics.Branching.value' (step i u) j := by
  simp only [position,
    displace_append_singleton, add_assoc]

theorem position_append_two
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u : 𝕍) (j k : ℕ) :
    position initial step i (u ++ [j, k]) =
      position initial step i u +
        Combinatorics.Branching.value' (step i u) j +
        Combinatorics.Branching.value' (step i (u ++ [j])) k := by
  unfold position displace
  rw [displaceRoot_append_two]
  simp only [add_assoc]

theorem displace_append
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedStepField Root X) (i : Root)
    (u v : 𝕍) :
    displace step i (u ++ v) =
      displace step i u +
        displaceRoot (fun w => step i (u ++ w)) v := by
  exact displaceRoot_append (step i) u v

theorem position_append
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedStepField Root X)
    (i : Root) (u v : 𝕍) :
    position initial step i (u ++ v) =
      position initial step i u +
        displaceRoot (fun w => step i (u ++ w)) v := by
  unfold position
  rw [displace_append]
  simp only [add_assoc]

end RootIndexed

end ProbabilityTheory.BranchingRandomWalk

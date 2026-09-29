module

public import Combinatorics.BranchingWalk.Basic.Position

@[expose] public section

/-!
# Updating one generation of a branching step field

A recursive coupling may install new offspring steps at the currently exposed
parents without changing any position already constructed.  `updateGeneration`
replaces exactly the coordinates at one address depth.  The invariance lemmas
below are deterministic and therefore belong below the probability layer.
-/

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

/-- Replace exactly the steps at addresses of length `n`. -/
def StepField.updateGeneration {α X : Type*} (n : ℕ)
    (replacement fallback : StepField α X) : StepField α X :=
  fun u => if u.length = n then replacement u else fallback u

@[simp] theorem StepField.updateGeneration_eq {α X : Type*} (n : ℕ)
    (replacement fallback : StepField α X) (u : TreeNode α)
    (hu : u.length = n) :
    replacement.updateGeneration n fallback u = replacement u := by
  simp [StepField.updateGeneration, hu]

@[simp] theorem StepField.updateGeneration_ne {α X : Type*} (n : ℕ)
    (replacement fallback : StepField α X) (u : TreeNode α)
    (hu : u.length ≠ n) :
    replacement.updateGeneration n fallback u = fallback u := by
  simp [StepField.updateGeneration, hu]

@[simp] theorem StepField.updateGeneration_of_lt {α X : Type*} (n : ℕ)
    (replacement fallback : StepField α X) (u : TreeNode α)
    (hu : u.length < n) :
    replacement.updateGeneration n fallback u = fallback u :=
  StepField.updateGeneration_ne n replacement fallback u (Nat.ne_of_lt hu)

/-- Updating depth `n` does not change displacement along a path that ends no
later than depth `n`: displacement reads the steps at strict prefixes only. -/
theorem displaceWith_updateGeneration_of_le
    {α Mark Position : Type*} [AddCommMonoid Position]
    (d : Mark → Position) (n : ℕ)
    (replacement fallback : StepField α Mark)
    (v p : TreeNode α) (hvp : v.length + p.length ≤ n) :
    displaceWith d (replacement.updateGeneration n fallback) v p =
      displaceWith d fallback v p := by
  induction p generalizing v with
  | nil => rfl
  | cons i p ih =>
      have hv : v.length < n := by
        simp only [List.length_cons] at hvp
        omega
      rw [displaceWith_cons, displaceWith_cons,
        StepField.updateGeneration_of_lt n replacement fallback v hv]
      apply congrArg (fun z => value' ((fallback v).map d) i + z)
      apply ih (v := v ++ [i])
      simp only [List.length_append, List.length_singleton]
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hvp

/-- Root displacement is unchanged through depth `n` when only the steps at
exactly depth `n` are replaced. -/
theorem displaceWith_updateGeneration_root_of_le
    {α Mark Position : Type*} [AddCommMonoid Position]
    (d : Mark → Position) (n : ℕ)
    (replacement fallback : StepField α Mark)
    (u : TreeNode α) (hu : u.length ≤ n) :
    displaceWith d (replacement.updateGeneration n fallback) [] u =
      displaceWith d fallback [] u := by
  apply displaceWith_updateGeneration_of_le d n replacement fallback [] u
  simpa using hu

namespace RootIndexed

/-- Update one address depth independently below every root. -/
def StepField.updateGeneration {Root α X : Type*} (n : ℕ)
    (replacement fallback : Root → Combinatorics.Branching.StepField α X) :
    Root → Combinatorics.Branching.StepField α X :=
  fun r => (replacement r).updateGeneration n (fallback r)

@[simp] theorem StepField.updateGeneration_apply
    {Root α X : Type*} (n : ℕ)
    (replacement fallback : Root → Combinatorics.Branching.StepField α X)
    (r : Root) (u : TreeNode α) :
    RootIndexed.StepField.updateGeneration n replacement fallback r u =
      if u.length = n then replacement r u else fallback r u :=
  rfl

/-- Positions through generation `n` are invariant under an update of the
steps owned by generation-`n` parents. -/
theorem BranchingWalk.position_updateGeneration_of_le
    {Root α Mark Position : Type*} [AddCommMonoid Position]
    (d : Mark → Position) (n : ℕ)
    (initial : Root → Position)
    (replacement fallback : Root → Combinatorics.Branching.StepField α Mark)
    (r : Root) (u : TreeNode α) (hu : u.length ≤ n) :
    (RootIndexed.BranchingWalk.ofStepField initial
      (RootIndexed.StepField.updateGeneration n replacement fallback)).position
        d r u =
      (RootIndexed.BranchingWalk.ofStepField initial fallback).position d r u := by
  rw [RootIndexed.BranchingWalk.position, RootIndexed.BranchingWalk.position]
  congr 1
  exact displaceWith_updateGeneration_root_of_le d n
    (replacement r) (fallback r) u hu

end RootIndexed

end Combinatorics.Branching

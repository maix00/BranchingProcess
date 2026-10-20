/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Basic
public import Combinatorics.BranchingWalk.Step.Basic
public import Probability.BranchingRandomWalk.Step.Position.Measurability
public import Combinatorics.BranchingWalk.Basic.Position.DisplacementMap
public import Combinatorics.BranchingWalk.Basic.Map
public import Combinatorics.BranchingWalk.StepField
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Positions on root-indexed branching step fields

The public declarations in
`ProbabilityTheory.BranchingRandomWalk.RootIndexed` are:

- `displace`, `position`: total displacement and initial-position-shifted
  position at a root and address.
- `displace?`, `position?`: the corresponding partial values, equal to
  `some` of the total value exactly when the address survives.
- `displace?_eq_some_iff`, `displace?_eq_none_iff`,
  `position?_eq_some_iff`, `position?_eq_none_iff`: characterize the option
  results by survival along the address.
- `displace_reindex`, `displace?_reindex`, `position_reindex`,
  `position?_reindex`: reindexing roots by $f$ changes evaluation at $i$ to
  evaluation at $f(i)$.
- `displace_nil`, `position_root`: the root displacement is $0$ and its
  position is its initial position.
- `displace_append_singleton`, `position_append_singleton`: appending one
  child adds the mapped mark at the current address.
- `position_append_two`: appending two children adds their successive mapped
  marks.
- `displace_append`, `position_append`: concatenating addresses adds the
  displacement along the suffix in the field rebased at the prefix.
- `position_eq_initial_add_mark`: unfolds the position as the initial value
  plus the displacement.

For a root-indexed step field and a mark map $d$, `displace` sums the mapped
marks along a Ulam--Harris address, and `position` adds the root's initial
position. Their option-valued counterparts record whether that address
survives. All position-valued statements require only an additive commutative
monoid.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

namespace RootIndexed

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

def displace {Root α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (d : Mark → Position) (step : RootIndexed.StepField Root α Mark) (i : Root) (u : TreeNode α) : Position :=
  Combinatorics.Branching.displaceWith d (step i) [] u

def displace? {Root α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (d : Mark → Position) (step : RootIndexed.StepField Root α Mark) (i : Root) (u : TreeNode α) : Option Position :=
  Combinatorics.Branching.displaceWith? d (step i) [] u

theorem displace?_eq_some_iff
    {Root α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (d : Mark → Position) (step : RootIndexed.StepField Root α Mark) (i : Root) (u : TreeNode α) :
    displace? d step i u =
        some (displace d step i u) ↔
      surviveAlong (step i) [] u := by
  rw [displace?, displace,
    Combinatorics.Branching.displaceWith?_eq_some_iff]

theorem displace?_eq_none_iff
    {Root α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (d : Mark → Position) (step : RootIndexed.StepField Root α Mark) (i : Root) (u : TreeNode α) :
    displace? d step i u = none ↔
      ¬ surviveAlong (step i) [] u :=
  Combinatorics.Branching.displaceWith?_eq_none_iff d (step i) [] u

theorem displace_reindex
    {Root NewRoot α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (d : Mark → Position) (step : RootIndexed.StepField Root α Mark)
    (f : NewRoot → Root) (i : NewRoot) (u : TreeNode α) :
    displace d (step.reindex f) i u =
      displace d step (f i) u := by
  rfl

@[simp] theorem displace_nil
    {Root α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (d : Mark → Position) (step : RootIndexed.StepField Root α Mark) (i : Root) :
    displace d step i [] = 0 := by
  exact Combinatorics.Branching.displaceWith_nil d (step i) []

theorem displace_append_singleton
    {Root α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (d : Mark → Position) (step : RootIndexed.StepField Root α Mark) (i : Root) (u : TreeNode α) (j : α) :
    displace d step i (u ++ [j]) =
      displace d step i u +
        Combinatorics.Branching.value' ((step i u).map d) j := by
  exact Combinatorics.Branching.displace_append_singleton ((step i).map d) u j

def position {Root α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position) (step : RootIndexed.StepField Root α Mark)
    (i : Root) (u : TreeNode α) : Position :=
  initial i + displace d step i u

def position? {Root α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position) (step : RootIndexed.StepField Root α Mark)
    (i : Root) (u : TreeNode α) : Option Position :=
  (displace? d step i u).map (initial i + ·)

theorem displace?_reindex
    {Root NewRoot α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (d : Mark → Position) (step : RootIndexed.StepField Root α Mark)
    (f : NewRoot → Root) (i : NewRoot) (u : TreeNode α) :
    displace? d (step.reindex f) i u =
      displace? d step (f i) u := by
  rfl

theorem position?_reindex
    {Root NewRoot α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position) (step : RootIndexed.StepField Root α Mark)
    (f : NewRoot → Root) (i : NewRoot) (u : TreeNode α) :
    position? (initial ∘ f) d (step.reindex f) i u =
      position? initial d step (f i) u := by
  rfl

theorem position?_eq_some_iff
    {Root α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position) (step : RootIndexed.StepField Root α Mark)
    (i : Root) (u : TreeNode α) :
    position? initial d step i u =
        some (position initial d step i u) ↔
      surviveAlong (step i) [] u := by
  by_cases h : surviveAlong (step i) [] u
  · have hsome := (displace?_eq_some_iff d step i u).mpr h
    simp [position?, position, hsome]
    exact h
  · have hnone := (displace?_eq_none_iff d step i u).mpr h
    simp [position?, hnone]
    exact h

theorem position?_eq_none_iff
    {Root α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position) (step : RootIndexed.StepField Root α Mark)
    (i : Root) (u : TreeNode α) :
    position? initial d step i u = none ↔
      ¬ surviveAlong (step i) [] u := by
  by_cases h : surviveAlong (step i) [] u
  · have hsome := (displace?_eq_some_iff d step i u).mpr h
    simp [position?, hsome]
    exact h
  · have hnone := (displace?_eq_none_iff d step i u).mpr h
    simp [position?, hnone]
    exact h

theorem position_reindex
    {Root NewRoot α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position) (step : RootIndexed.StepField Root α Mark)
    (f : NewRoot → Root) (i : NewRoot) (u : TreeNode α) :
    position (initial ∘ f) d (step.reindex f) i u =
      position initial d step (f i) u := by
  rfl

theorem position_eq_initial_add_mark
    {Root α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position) (step : RootIndexed.StepField Root α Mark)
    (i : Root) (u : TreeNode α) :
    position initial d step i u =
      initial i + Combinatorics.Branching.displaceWith d (step i) [] u := by
  simp [position, displace]

@[simp] theorem position_root
    {Root α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position) (step : RootIndexed.StepField Root α Mark) (i : Root) :
    position initial d step i [] = initial i := by
  simp [position]

theorem position_append_singleton
    {Root α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position) (step : RootIndexed.StepField Root α Mark)
    (i : Root) (u : TreeNode α) (j : α) :
    position initial d step i (u ++ [j]) =
      position initial d step i u +
        Combinatorics.Branching.value' ((step i u).map d) j := by
  simp only [position,
    displace_append_singleton, add_assoc]

theorem position_append_two
    {Root α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position) (step : RootIndexed.StepField Root α Mark)
    (i : Root) (u : TreeNode α) (j k : α) :
    position initial d step i (u ++ [j, k]) =
      position initial d step i u +
        Combinatorics.Branching.value' ((step i u).map d) j +
        Combinatorics.Branching.value' ((step i (u ++ [j])).map d) k := by
  unfold position displace Combinatorics.Branching.displaceWith
  rw [Combinatorics.Branching.displace_append_two]
  simp only [Combinatorics.Branching.StepField.map_apply, add_assoc]

theorem displace_append
    {Root α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (d : Mark → Position) (step : RootIndexed.StepField Root α Mark) (i : Root)
    (u v : TreeNode α) :
    displace d step i (u ++ v) =
      displace d step i u +
        Combinatorics.Branching.displaceWith d (fun w => step i (u ++ w)) [] v := by
  change Combinatorics.Branching.displaceWith d (step i) [] (u ++ v) =
    Combinatorics.Branching.displaceWith d (step i) [] u +
      Combinatorics.Branching.displaceWith d (fun w => step i (u ++ w)) [] v
  unfold Combinatorics.Branching.displaceWith
  rw [Combinatorics.Branching.displace_append]
  congr 1
  change Combinatorics.Branching.displace ((step i).map d) u v =
    Combinatorics.Branching.displace
      (fun w => ((step i).map d) (u ++ w)) [] v
  symm
  simpa using
    (Combinatorics.Branching.displace_rebase ((step i).map d) u [] v)

theorem position_append
    {Root α : Type*} {Mark Position : Type*} [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position) (step : RootIndexed.StepField Root α Mark)
    (i : Root) (u v : TreeNode α) :
    position initial d step i (u ++ v) =
      position initial d step i u +
        Combinatorics.Branching.displaceWith d (fun w => step i (u ++ w)) [] v := by
  unfold position
  rw [displace_append]
  simp only [add_assoc]

end RootIndexed

end ProbabilityTheory.BranchingRandomWalk

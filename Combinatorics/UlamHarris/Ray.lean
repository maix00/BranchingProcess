/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.List.Induction
public import Mathlib.Data.Set.Basic

/-!
# Infinite paths of tree addresses

## Public declarations

In `Combinatorics.UlamHarris`:

* `lineagePrefix f n` is the address `[f 0, …, f (n-1)]`;
  `lineagePrefix_zero`, `lineagePrefix_succ`, and `length_lineagePrefix`
  give its empty prefix, one-step extension, and length `n`.
* `lineagePrefix_prefix` states `n ≤ m → lineagePrefix f n <+: lineagePrefix f m`.
* `IsRay C f` means `∀ n, lineagePrefix f n ∈ C`: all prefixes of the
  infinite child-index sequence `f` belong to the node set `C`.
  `IsRay.mono` states `C ⊆ D → IsRay C f → IsRay D f`.
* `existsUnique_isRay_of_unique_child` proves `∃! f, IsRay C f` when
  `[] ∈ C` and each `u ∈ C` has exactly one child in `C`.
* `IsRay.eq_range_of_unique_child` identifies `C = range (lineagePrefix f)`
  when `C` is closed under taking parents and has unique continuation.

No order, finite branching, or survival law is required. In particular,
`IsRay T.carrier f` describes a realized infinite path of a deterministic
Ulam--Harris tree, and the same predicate works for a tree with arbitrary
child-index gaps.
-/

@[expose] public section

namespace Combinatorics.UlamHarris

variable {α : Type*}

/-- The first `n` entries of an infinite sequence of child indices. -/
def lineagePrefix (lineage : ℕ → α) (n : ℕ) : TreeNode α :=
  match n with
  | 0 => []
  | n + 1 => lineagePrefix lineage n ++ [lineage n]

@[simp] theorem lineagePrefix_zero (f : ℕ → α) : lineagePrefix f 0 = [] := rfl

@[simp] theorem lineagePrefix_succ (f : ℕ → α) (n : ℕ) :
    lineagePrefix f (n + 1) = lineagePrefix f n ++ [f n] := rfl

@[simp] theorem length_lineagePrefix (f : ℕ → α) (n : ℕ) :
    (lineagePrefix f n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

theorem lineagePrefix_prefix (f : ℕ → α) {n m : ℕ} (hnm : n ≤ m) :
    lineagePrefix f n <+: lineagePrefix f m := by
  induction hnm with
  | refl => exact List.prefix_rfl
  | step _ ih => exact ih.trans (List.prefix_append _ _)

/-- An infinite path all of whose finite prefixes belong to the specified node set. -/
def IsRay (C : Set (TreeNode α)) (f : ℕ → α) : Prop :=
  ∀ n, lineagePrefix f n ∈ C

theorem IsRay.mono {C D : Set (TreeNode α)} {f : ℕ → α}
    (hf : IsRay C f) (hCD : C ⊆ D) : IsRay D f := fun n => hCD (hf n)

/-- A rooted carrier with exactly one continuing child at each of its nodes has one ray. -/
theorem existsUnique_isRay_of_unique_child (C : Set (TreeNode α)) (hroot : [] ∈ C)
    (hchild : ∀ u ∈ C, ∃! i, u ++ [i] ∈ C) : ∃! f, IsRay C f := by
  classical
  let child (u : {u // u ∈ C}) : α := Classical.choose (hchild u.1 u.2)
  have hmem (u : {u // u ∈ C}) : u.1 ++ [child u] ∈ C :=
    (Classical.choose_spec (hchild u.1 u.2)).1
  let next (u : {u // u ∈ C}) : {u // u ∈ C} := ⟨u.1 ++ [child u], hmem u⟩
  let root : {u // u ∈ C} := ⟨[], hroot⟩
  let f (n : ℕ) := child (next^[n] root)
  have hprefix : ∀ n, lineagePrefix f n = (next^[n] root).1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [lineagePrefix_succ, ih, Function.iterate_succ_apply']
  have hf : IsRay C f := by
    intro n
    rw [hprefix]
    exact (next^[n] root).2
  refine ⟨f, hf, ?_⟩
  intro g hg
  have hsame : ∀ n, lineagePrefix g n = lineagePrefix f n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [lineagePrefix_succ, lineagePrefix_succ, ih]
      congr 1
      have hgc : lineagePrefix f n ++ [g n] ∈ C := by
        rw [← ih]
        exact hg (n + 1)
      have hfc : lineagePrefix f n ++ [f n] ∈ C := hf (n + 1)
      exact congrArg (fun i => [i]) ((hchild _ (hf n)).unique hgc hfc)
  funext n
  have hn := hsame (n + 1)
  rw [lineagePrefix_succ, lineagePrefix_succ, hsame n] at hn
  exact List.singleton_inj.mp (List.append_cancel_left hn)

/-- With ancestor closure and unique continuation, every carrier node lies on the ray. -/
theorem IsRay.eq_range_of_unique_child {C : Set (TreeNode α)} {f : ℕ → α}
    (hf : IsRay C f)
    (hchild : ∀ u ∈ C, ∃! i, u ++ [i] ∈ C)
    (hparent : ∀ u i, u ++ [i] ∈ C → u ∈ C) : C = Set.range (lineagePrefix f) := by
  have hprefix : ∀ u ∈ C, lineagePrefix f u.length = u := by
    intro u
    induction u using List.reverseRecOn with
    | nil => intro _; rfl
    | append_singleton u i ih =>
      intro hui
      have hu := hparent u i hui
      have he := ih hu
      have hi : i = f u.length := (hchild u hu).unique hui (by
        simpa only [lineagePrefix_succ, he] using hf (u.length + 1))
      simp only [List.length_append, List.length_singleton, lineagePrefix_succ, he, hi]
  ext u
  constructor
  · intro hu
    exact ⟨u.length, hprefix u hu⟩
  · rintro ⟨n, rfl⟩
    exact hf n

end Combinatorics.UlamHarris

end

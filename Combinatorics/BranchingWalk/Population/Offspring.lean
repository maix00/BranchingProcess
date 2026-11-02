/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Data.Set.Function
public import Combinatorics.UlamHarris.Relation

/-!
# One-generation offspring addresses

## Public declarations

For a set `parents` of root-indexed addresses and a slot set `slots p` assigned
to each parent, the eligible pair set and child-address set are
$\{(p,i)\mid p\in\mathrm{parents},\ i\in\mathrm{slots}(p)\}$ and
$\{\operatorname{childAddress}(p,i)\mid p\in\mathrm{parents},\
i\in\mathrm{slots}(p)\}$:

* `Combinatorics.Branching.Population.offspringPairSet parents slots` is the
  set of eligible parent-slot pairs, with membership characterized by
  `mem_offspringPairSet`.
* `Combinatorics.Branching.Population.offspringAddressSet parents slots` is
  the set of child addresses obtained by appending each eligible slot to its
  parent; `mem_offspringAddressSet` characterizes its members.

These set-valued constructions have no finiteness, ordering, selection, or
probability assumptions. Root-preserving child-address operations are defined
in `Combinatorics.UlamHarris.RootIndexed`.
-/

@[expose] public section

namespace Combinatorics.Branching.Population

open Combinatorics.UlamHarris

variable {Root α : Type*}

/-- Eligible parent-slot pairs for one generation. -/
def offspringPairSet
    (parents : Set (RootIndexed.TreeNode Root α))
    (slots : RootIndexed.TreeNode Root α → Set α) :
    Set (RootIndexed.TreeNode Root α × α) :=
  {pi | pi.1 ∈ parents ∧ pi.2 ∈ slots pi.1}

@[simp] theorem mem_offspringPairSet
    {parents : Set (RootIndexed.TreeNode Root α)}
    {slots : RootIndexed.TreeNode Root α → Set α}
    {p : RootIndexed.TreeNode Root α} {i : α} :
    (p, i) ∈ offspringPairSet parents slots ↔ p ∈ parents ∧ i ∈ slots p :=
  Iff.rfl

/-- Child addresses generated from an arbitrary parent set and local slot
sets. -/
def offspringAddressSet
    (parents : Set (RootIndexed.TreeNode Root α))
    (slots : RootIndexed.TreeNode Root α → Set α) :
    Set (RootIndexed.TreeNode Root α) :=
  (fun pi : RootIndexed.TreeNode Root α × α =>
    RootIndexed.childAddress pi.1 pi.2) '' offspringPairSet parents slots

@[simp] theorem mem_offspringAddressSet
    {parents : Set (RootIndexed.TreeNode Root α)}
    {slots : RootIndexed.TreeNode Root α → Set α}
    {q : RootIndexed.TreeNode Root α} :
    q ∈ offspringAddressSet parents slots ↔
      ∃ p ∈ parents, ∃ i ∈ slots p, q = RootIndexed.childAddress p i := by
  constructor
  · rintro ⟨⟨p, i⟩, ⟨hp, hi⟩, rfl⟩
    exact ⟨p, hp, i, hi, rfl⟩
  · rintro ⟨p, hp, i, hi, rfl⟩
    exact ⟨(p, i), ⟨hp, hi⟩, rfl⟩

end Combinatorics.Branching.Population

end

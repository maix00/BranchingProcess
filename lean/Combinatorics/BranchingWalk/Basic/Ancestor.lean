/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.Descendant

/-!
# Ancestor relations

Ancestor sets and generation slices, defined as the reverse of descendant relations.
-/

@[expose] public section

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

variable {Root α Mark Position : Type*}

/-- `q` is an ancestor of `p` when `p` is a descendant of `q`. The relation is the converse of
`IsDescendant`, kept as its own name because the statements about ancestors read the other way. -/
def IsAncestor (β : RootIndexed.BranchingWalk Root α Mark Position) (p q : RootIndexed.TreeNode Root α) : Prop :=
  IsDescendant β q p

theorem isAncestor_iff_isDescendant (β : RootIndexed.BranchingWalk Root α Mark Position)
    (p q : RootIndexed.TreeNode Root α) : IsAncestor β p q ↔ IsDescendant β q p := Iff.rfl

/-- Every particle is an ancestor of itself. -/
theorem isAncestor_refl (β : RootIndexed.BranchingWalk Root α Mark Position) (p : RootIndexed.TreeNode Root α) :
    IsAncestor β p p :=
  isDescendant_refl β p

/-- An ancestor sits at the same root as the particle it is an ancestor of. -/
theorem fst_eq_of_isAncestor (β : RootIndexed.BranchingWalk Root α Mark Position)
    {p q : RootIndexed.TreeNode Root α} (h : IsAncestor β p q) : q.1 = p.1 :=
  (fst_eq_of_isDescendant β h).symm

/-- An ancestor's generation is the generation of the descendant minus the generations between them,
read the other way round from `generation_eq_generation_add_of_isDescendant`. -/
theorem generation_eq_generation_add_of_isAncestor (β : RootIndexed.BranchingWalk Root α Mark Position)
    {p q : RootIndexed.TreeNode Root α} (h : IsAncestor β p q) :
    generation p.2 = generation q.2 + generationAfter q.2 p.2 :=
  generation_eq_generation_add_of_isDescendant β h

/-- Ancestors compose: an ancestor of an ancestor is an ancestor, which is what makes the ancestors
of a particle a chain. -/
theorem isAncestor_trans (β : RootIndexed.BranchingWalk Root α Mark Position)
    {p q r : RootIndexed.TreeNode Root α} (hpq : IsAncestor β p q) (hqr : IsAncestor β q r) :
    IsAncestor β p r :=
  isDescendant_trans β hqr hpq

/-- The ancestors of a particle: the particles of which it is a descendant. -/
def ancestors (β : RootIndexed.BranchingWalk Root α Mark Position) (p : RootIndexed.TreeNode Root α) :
    Set (RootIndexed.TreeNode Root α) :=
  {q | IsAncestor β p q}

@[simp] theorem mem_ancestors_iff (β : RootIndexed.BranchingWalk Root α Mark Position)
    (p q : RootIndexed.TreeNode Root α) : q ∈ ancestors β p ↔ IsDescendant β q p := Iff.rfl

/-- The ancestors of a particle exactly `k` generations above it. -/
def ancestorsAt (β : RootIndexed.BranchingWalk Root α Mark Position) (p : RootIndexed.TreeNode Root α) (k : ℕ) :
    Set (RootIndexed.TreeNode Root α) :=
  {q | IsAncestor β p q ∧ generationAfter q.2 p.2 = k}

@[simp] theorem mem_ancestorsAt_iff (β : RootIndexed.BranchingWalk Root α Mark Position)
    (p : RootIndexed.TreeNode Root α) (k : ℕ) (q : RootIndexed.TreeNode Root α) :
    q ∈ ancestorsAt β p k ↔ IsAncestor β p q ∧ generationAfter q.2 p.2 = k :=
  Iff.rfl

/-- A distance slice consists of ancestors. -/
theorem mem_ancestors_of_mem_ancestorsAt (β : RootIndexed.BranchingWalk Root α Mark Position)
    {p : RootIndexed.TreeNode Root α} {k : ℕ} {q : RootIndexed.TreeNode Root α} (hq : q ∈ ancestorsAt β p k) :
    q ∈ ancestors β p :=
  hq.1

/-- On a distance slice, the number of generations above the particle is the one cutting it. -/
theorem generationAfter_of_mem_ancestorsAt (β : RootIndexed.BranchingWalk Root α Mark Position)
    {p : RootIndexed.TreeNode Root α} {k : ℕ} {q : RootIndexed.TreeNode Root α} (hq : q ∈ ancestorsAt β p k) :
    generationAfter q.2 p.2 = k :=
  hq.2

/-- Different distances above a particle give disjoint sets of ancestors. -/
theorem disjoint_ancestorsAt (β : RootIndexed.BranchingWalk Root α Mark Position) (p : RootIndexed.TreeNode Root α)
    {k l : ℕ} (hkl : k ≠ l) : Disjoint (ancestorsAt β p k) (ancestorsAt β p l) := by
  rw [Set.disjoint_left]
  intro q hq hr
  exact hkl (by rw [← hq.2, hr.2])

/-- An ancestor lies in one of the distance slices, so those slices partition the ancestors. -/
theorem mem_ancestors_iff_exists_mem_ancestorsAt (β : RootIndexed.BranchingWalk Root α Mark Position)
    (p q : RootIndexed.TreeNode Root α) :
    q ∈ ancestors β p ↔ ∃ k : ℕ, q ∈ ancestorsAt β p k :=
  ⟨fun hq => ⟨generationAfter q.2 p.2, hq, rfl⟩, fun ⟨_, hq⟩ => hq.1⟩


end Combinatorics.Branching

end

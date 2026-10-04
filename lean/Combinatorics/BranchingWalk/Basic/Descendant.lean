/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.Definitions
public import Combinatorics.UlamHarris.Generation

/-!
# Descendant relations

Descendant sets and generation slices for root-indexed branching walks.
-/

@[expose] public section

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

variable {Root α Mark Position : Type*}

/-- `q` is a descendant of `p` in the walk: the two are particles of one root and the address of `q`
is the address of `p` followed by a path that survives from it along that root's step field. -/
def IsDescendant (β : RootIndexed.BranchingWalk Root α Mark Position) (p q : RootIndexed.TreeNode Root α) : Prop :=
  ∃ t, q = (p.1, p.2 ++ t) ∧ surviveAlong (β.step p.1) p.2 t

/-- A descendant sits at the same root as its ancestor. -/
theorem fst_eq_of_isDescendant (β : RootIndexed.BranchingWalk Root α Mark Position)
    {p q : RootIndexed.TreeNode Root α} (h : IsDescendant β p q) : q.1 = p.1 := by
  obtain ⟨t, ht, -⟩ := h
  rw [ht]

/-- A descendant's address is the ancestor's address followed by a surviving path. -/
theorem exists_snd_eq_append_of_isDescendant (β : RootIndexed.BranchingWalk Root α Mark Position)
    {p q : RootIndexed.TreeNode Root α} (h : IsDescendant β p q) :
    ∃ t, q.2 = p.2 ++ t ∧ surviveAlong (β.step p.1) p.2 t := by
  obtain ⟨t, ht, hs⟩ := h
  exact ⟨t, ((Prod.mk.injEq _ _ _ _).mp ht).2, hs⟩

/-- Every particle is a descendant of itself. -/
theorem isDescendant_refl (β : RootIndexed.BranchingWalk Root α Mark Position) (p : RootIndexed.TreeNode Root α) :
    IsDescendant β p p :=
  ⟨[], by simp, trivial⟩

/-- The descendants of a particle at one step are its children whose slot survives. -/
theorem isDescendant_child_iff (β : RootIndexed.BranchingWalk Root α Mark Position) (p : RootIndexed.TreeNode Root α)
    (i : α) : IsDescendant β p (p.1, p.2 ++ [i]) ↔ survive (β.step p.1 p.2) i := by
  constructor
  · rintro ⟨t, ht, hs⟩
    have ht2 : p.2 ++ [i] = p.2 ++ t := ((Prod.mk.injEq _ _ _ _).mp ht).2
    have hti : t = [i] := (List.append_cancel_left ht2).symm
    subst hti
    simpa [surviveAlong] using hs
  · intro hi
    exact ⟨[i], rfl, by simpa [surviveAlong] using hi⟩

/-- Descendants compose: a descendant of a descendant is a descendant. -/
theorem isDescendant_trans (β : RootIndexed.BranchingWalk Root α Mark Position)
    {p q r : RootIndexed.TreeNode Root α} (hpq : IsDescendant β p q) (hqr : IsDescendant β q r) :
    IsDescendant β p r := by
  obtain ⟨t, ht, hs⟩ := hpq
  obtain ⟨t', ht', hs'⟩ := hqr
  refine ⟨t ++ t', ?_, ?_⟩
  · rw [ht', ht, List.append_assoc]
  · rw [surviveAlong_append]
    have hq1 : q.1 = p.1 := ((Prod.mk.injEq _ _ _ _).mp ht).1
    have hq2 : q.2 = p.2 ++ t := ((Prod.mk.injEq _ _ _ _).mp ht).2
    refine ⟨hs, ?_⟩
    rw [← hq1, ← hq2]
    exact hs'

/-- A descendant's own generation is the generation of its ancestor plus the generations between
them, so the number of generations below an ancestor is known on every descendant. -/
theorem generation_eq_generation_add_of_isDescendant (β : RootIndexed.BranchingWalk Root α Mark Position)
    {p q : RootIndexed.TreeNode Root α} (h : IsDescendant β p q) :
    generation q.2 = generation p.2 + generationAfter p.2 q.2 := by
  obtain ⟨t, ht, -⟩ := h
  have hq : q.2 = p.2 ++ t := ((Prod.mk.injEq _ _ _ _).mp ht).2
  rw [hq, generation_append,
    generationAfter_eq_length (u := p.2) (v := p.2 ++ t) (p := t) rfl]
  simp [generation]

/-- The descendants of a particle, as a set of particles: the same index as the cloud's particles. -/
def descendants (β : RootIndexed.BranchingWalk Root α Mark Position) (p : RootIndexed.TreeNode Root α) :
    Set (RootIndexed.TreeNode Root α) :=
  {q | IsDescendant β p q}

@[simp] theorem mem_descendants_iff (β : RootIndexed.BranchingWalk Root α Mark Position)
    (p q : RootIndexed.TreeNode Root α) : q ∈ descendants β p ↔ IsDescendant β p q := Iff.rfl

/-- The descendants of a particle exactly `k` generations below it. -/
def descendantsAt (β : RootIndexed.BranchingWalk Root α Mark Position) (p : RootIndexed.TreeNode Root α) (k : ℕ) :
    Set (RootIndexed.TreeNode Root α) :=
  {q | IsDescendant β p q ∧ generationAfter p.2 q.2 = k}

@[simp] theorem mem_descendantsAt_iff (β : RootIndexed.BranchingWalk Root α Mark Position)
    (p : RootIndexed.TreeNode Root α) (k : ℕ) (q : RootIndexed.TreeNode Root α) :
    q ∈ descendantsAt β p k ↔ IsDescendant β p q ∧ generationAfter p.2 q.2 = k :=
  Iff.rfl

/-- A generation slice consists of descendants. -/
theorem mem_descendants_of_mem_descendantsAt (β : RootIndexed.BranchingWalk Root α Mark Position)
    {p : RootIndexed.TreeNode Root α} {k : ℕ} {q : RootIndexed.TreeNode Root α} (hq : q ∈ descendantsAt β p k) :
    q ∈ descendants β p :=
  hq.1

/-- On a generation slice, the number of generations below the ancestor is the one cutting it. -/
theorem generationAfter_of_mem_descendantsAt (β : RootIndexed.BranchingWalk Root α Mark Position)
    {p : RootIndexed.TreeNode Root α} {k : ℕ} {q : RootIndexed.TreeNode Root α} (hq : q ∈ descendantsAt β p k) :
    generationAfter p.2 q.2 = k :=
  hq.2

/-- Different generations below a particle are disjoint. -/
theorem disjoint_descendantsAt (β : RootIndexed.BranchingWalk Root α Mark Position) (p : RootIndexed.TreeNode Root α)
    {k l : ℕ} (hkl : k ≠ l) : Disjoint (descendantsAt β p k) (descendantsAt β p l) := by
  rw [Set.disjoint_left]
  intro q hq hr
  exact hkl (by rw [← hq.2, hr.2])

/-- A descendant lies in one of the generation slices, so those slices partition the descendants. -/
theorem mem_descendants_iff_exists_mem_descendantsAt (β : RootIndexed.BranchingWalk Root α Mark Position)
    (p q : RootIndexed.TreeNode Root α) :
    q ∈ descendants β p ↔ ∃ k : ℕ, q ∈ descendantsAt β p k :=
  ⟨fun hq => ⟨generationAfter p.2 q.2, hq, rfl⟩, fun ⟨_, hq⟩ => hq.1⟩

/-- The descendants of a particle within one root, as a set of addresses: the derived single-ancestor
form of `descendants`, read off the particles by keeping the root fixed. -/
def descendantsOfRoot (β : RootIndexed.BranchingWalk Root α Mark Position) (r : Root) (u : TreeNode α) :
    Set (TreeNode α) :=
  {v | IsDescendant β (r, u) (r, v)}

@[simp] theorem mem_descendantsOfRoot_iff (β : RootIndexed.BranchingWalk Root α Mark Position) (r : Root)
    (u v : TreeNode α) : v ∈ descendantsOfRoot β r u ↔ IsDescendant β (r, u) (r, v) := Iff.rfl

/-- The derived single-root form and the particle form describe the same descendants: an address of
the root `r` is below `u` exactly when the particle `(r, v)` is below `(r, u)`. -/
theorem mem_descendantsOfRoot_iff_mem_descendants (β : RootIndexed.BranchingWalk Root α Mark Position)
    (r : Root) (u v : TreeNode α) :
    v ∈ descendantsOfRoot β r u ↔ (r, v) ∈ descendants β (r, u) :=
  Iff.rfl

/-- The descendants of the root particle are the realized addresses of that root: this is the link
back to `surviveAlong`, and it is what makes "all surviving particles of a root" a special case of
"descendants of a particle". -/
theorem isDescendant_root_iff (β : RootIndexed.BranchingWalk Root α Mark Position) (r : Root)
    (v : TreeNode α) :
    IsDescendant β (r, []) (r, v) ↔ surviveAlong (β.step r) [] v := by
  constructor
  · rintro ⟨t, ht, hs⟩
    have hv : v = t := by
      simpa using ((Prod.mk.injEq _ _ _ _).mp ht).2
    rwa [hv]
  · intro hv
    exact ⟨v, by simp, hv⟩


end Combinatorics.Branching

end

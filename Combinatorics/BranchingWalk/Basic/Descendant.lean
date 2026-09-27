import Combinatorics.BranchingWalk.Basic.Definitions
import Combinatorics.UlamHarris.Generation

/-!
# Descendants of a particle in a branching walk

`IsDescendant β p q` says that the particle `q` is a descendant of the particle `p`: the two sit at
the same root and the address of `q` is the address of `p` followed by a path that survives along
that root's step field. The arguments are particles, so the notion carries the same index as
`Cloud.particles`, and the descendant sets `descendants β p` and their generation slices
`descendantsAt β p k` are subsets of that same type.

The single-ancestor reading, in which the addresses of one root are the object, is the derived form
`descendantsOfRoot`, tied to the particle form by `mem_descendantsOfRoot_iff_mem_descendants`.

The generations themselves are `generation` (the length of an address) and `generationAfter`
(the generations between a node and a descendant), which belong to the tree and live in
`UlamHarris/Tree/Generation.lean`.

The particles of the cloud `Cloud.ofBranchingWalk β time` are exactly the root-address pairs whose
address is a descendant of the empty address at a matching time; that link lives with the cloud,
since this folder does not know about time.
-/

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

variable {Root α X : Type*}

/-- `q` is a descendant of `p` in the walk: the two are particles of one root and the address of `q`
is the address of `p` followed by a path that survives from it along that root's step field. -/
def IsDescendant (β : RootIndexed.BranchingWalk Root α X) (p q : Root × TreeNode α) : Prop :=
  ∃ t, q = (p.1, p.2 ++ t) ∧ surviveAlong (β.step p.1) p.2 t

/-- A descendant sits at the same root as its ancestor. -/
theorem fst_eq_of_isDescendant (β : RootIndexed.BranchingWalk Root α X)
    {p q : Root × TreeNode α} (h : IsDescendant β p q) : q.1 = p.1 := by
  obtain ⟨t, ht, -⟩ := h
  rw [ht]

/-- A descendant's address is the ancestor's address followed by a surviving path. -/
theorem exists_snd_eq_append_of_isDescendant (β : RootIndexed.BranchingWalk Root α X)
    {p q : Root × TreeNode α} (h : IsDescendant β p q) :
    ∃ t, q.2 = p.2 ++ t ∧ surviveAlong (β.step p.1) p.2 t := by
  obtain ⟨t, ht, hs⟩ := h
  exact ⟨t, ((Prod.mk.injEq _ _ _ _).mp ht).2, hs⟩

/-- Every particle is a descendant of itself. -/
theorem isDescendant_refl (β : RootIndexed.BranchingWalk Root α X) (p : Root × TreeNode α) :
    IsDescendant β p p :=
  ⟨[], by simp, trivial⟩

/-- The descendants of a particle at one step are its children whose slot survives. -/
theorem isDescendant_child_iff (β : RootIndexed.BranchingWalk Root α X) (p : Root × TreeNode α)
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
theorem isDescendant_trans (β : RootIndexed.BranchingWalk Root α X)
    {p q r : Root × TreeNode α} (hpq : IsDescendant β p q) (hqr : IsDescendant β q r) :
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
theorem generation_eq_generation_add_of_isDescendant (β : RootIndexed.BranchingWalk Root α X)
    {p q : Root × TreeNode α} (h : IsDescendant β p q) :
    generation q.2 = generation p.2 + generationAfter p.2 q.2 := by
  obtain ⟨t, ht, -⟩ := h
  have hq : q.2 = p.2 ++ t := ((Prod.mk.injEq _ _ _ _).mp ht).2
  rw [hq, generation_append,
    generationAfter_eq_length (u := p.2) (v := p.2 ++ t) (p := t) rfl]
  simp [generation]

/-- The descendants of a particle, as a set of particles: the same index as the cloud's particles. -/
def descendants (β : RootIndexed.BranchingWalk Root α X) (p : Root × TreeNode α) :
    Set (Root × TreeNode α) :=
  {q | IsDescendant β p q}

@[simp] theorem mem_descendants_iff (β : RootIndexed.BranchingWalk Root α X)
    (p q : Root × TreeNode α) : q ∈ descendants β p ↔ IsDescendant β p q := Iff.rfl

/-- The descendants of a particle exactly `k` generations below it. -/
def descendantsAt (β : RootIndexed.BranchingWalk Root α X) (p : Root × TreeNode α) (k : ℕ) :
    Set (Root × TreeNode α) :=
  {q | IsDescendant β p q ∧ generationAfter p.2 q.2 = k}

@[simp] theorem mem_descendantsAt_iff (β : RootIndexed.BranchingWalk Root α X)
    (p : Root × TreeNode α) (k : ℕ) (q : Root × TreeNode α) :
    q ∈ descendantsAt β p k ↔ IsDescendant β p q ∧ generationAfter p.2 q.2 = k :=
  Iff.rfl

/-- A generation slice consists of descendants. -/
theorem mem_descendants_of_mem_descendantsAt (β : RootIndexed.BranchingWalk Root α X)
    {p : Root × TreeNode α} {k : ℕ} {q : Root × TreeNode α} (hq : q ∈ descendantsAt β p k) :
    q ∈ descendants β p :=
  hq.1

/-- On a generation slice, the number of generations below the ancestor is the one cutting it. -/
theorem generationAfter_of_mem_descendantsAt (β : RootIndexed.BranchingWalk Root α X)
    {p : Root × TreeNode α} {k : ℕ} {q : Root × TreeNode α} (hq : q ∈ descendantsAt β p k) :
    generationAfter p.2 q.2 = k :=
  hq.2

/-- Different generations below a particle are disjoint. -/
theorem disjoint_descendantsAt (β : RootIndexed.BranchingWalk Root α X) (p : Root × TreeNode α)
    {k l : ℕ} (hkl : k ≠ l) : Disjoint (descendantsAt β p k) (descendantsAt β p l) := by
  rw [Set.disjoint_left]
  intro q hq hr
  exact hkl (by rw [← hq.2, hr.2])

/-- A descendant lies in one of the generation slices, so those slices partition the descendants. -/
theorem mem_descendants_iff_exists_mem_descendantsAt (β : RootIndexed.BranchingWalk Root α X)
    (p q : Root × TreeNode α) :
    q ∈ descendants β p ↔ ∃ k : ℕ, q ∈ descendantsAt β p k :=
  ⟨fun hq => ⟨generationAfter p.2 q.2, hq, rfl⟩, fun ⟨_, hq⟩ => hq.1⟩

/-- The descendants of a particle within one root, as a set of addresses: the derived single-ancestor
form of `descendants`, read off the particles by keeping the root fixed. -/
def descendantsOfRoot (β : RootIndexed.BranchingWalk Root α X) (r : Root) (u : TreeNode α) :
    Set (TreeNode α) :=
  {v | IsDescendant β (r, u) (r, v)}

@[simp] theorem mem_descendantsOfRoot_iff (β : RootIndexed.BranchingWalk Root α X) (r : Root)
    (u v : TreeNode α) : v ∈ descendantsOfRoot β r u ↔ IsDescendant β (r, u) (r, v) := Iff.rfl

/-- The derived single-root form and the particle form describe the same descendants: an address of
the root `r` is below `u` exactly when the particle `(r, v)` is below `(r, u)`. -/
theorem mem_descendantsOfRoot_iff_mem_descendants (β : RootIndexed.BranchingWalk Root α X)
    (r : Root) (u v : TreeNode α) :
    v ∈ descendantsOfRoot β r u ↔ (r, v) ∈ descendants β (r, u) :=
  Iff.rfl

/-- The descendants of the root particle are the realized addresses of that root: this is the link
back to `surviveAlong`, and it is what makes "all surviving particles of a root" a special case of
"descendants of a particle". -/
theorem isDescendant_root_iff (β : RootIndexed.BranchingWalk Root α X) (r : Root)
    (v : TreeNode α) :
    IsDescendant β (r, []) (r, v) ↔ surviveAlong (β.step r) [] v := by
  constructor
  · rintro ⟨t, ht, hs⟩
    have hv : v = t := by
      simpa using ((Prod.mk.injEq _ _ _ _).mp ht).2
    rwa [hv]
  · intro hv
    exact ⟨v, by simp, hv⟩

/-- The surviving particles of the walk: the particles realized at some time, which are the
descendants of the always-realized root particles. This is the time-free carrier of the walk, the
one the cloud's time slices are cut out of. -/
def survivingParticles (β : RootIndexed.BranchingWalk Root α X) : Set (Root × TreeNode α) :=
  {p | IsDescendant β (p.1, []) p}

@[simp] theorem mem_survivingParticles_iff (β : RootIndexed.BranchingWalk Root α X)
    (p : Root × TreeNode α) : p ∈ survivingParticles β ↔ IsDescendant β (p.1, []) p := Iff.rfl

/-- An address of a root survives exactly when the particle it forms is a surviving particle. -/
theorem mem_survivingParticles_iff_surviveAlong (β : RootIndexed.BranchingWalk Root α X)
    (r : Root) (v : TreeNode α) :
    (r, v) ∈ survivingParticles β ↔ surviveAlong (β.step r) [] v := by
  rw [mem_survivingParticles_iff, isDescendant_root_iff]

/-- The surviving particles are the union of the descendants of the root particles. -/
theorem mem_survivingParticles_iff_exists_mem_descendants (β : RootIndexed.BranchingWalk Root α X)
    (p : Root × TreeNode α) :
    p ∈ survivingParticles β ↔ ∃ r : Root, p ∈ descendants β (r, []) := by
  constructor
  · intro hp
    exact ⟨p.1, by simpa using hp⟩
  · rintro ⟨r, hr⟩
    have hqr : IsDescendant β (r, []) p := (mem_descendants_iff β (r, []) p).mp hr
    have h1 : p.1 = r := fst_eq_of_isDescendant β hqr
    simpa [mem_survivingParticles_iff, h1] using hqr

/-- The surviving particles of one generation: the surviving particles whose address has generation
`k`. This is the time-free description of the walk's particles at a generation, the thing the cloud
read at the generations cuts out. -/
def survivingParticlesAt (β : RootIndexed.BranchingWalk Root α X) (k : ℕ) :
    Set (Root × TreeNode α) :=
  {p | p ∈ survivingParticles β ∧ generation p.2 = k}

@[simp] theorem mem_survivingParticlesAt_iff (β : RootIndexed.BranchingWalk Root α X) (k : ℕ)
    (p : Root × TreeNode α) :
    p ∈ survivingParticlesAt β k ↔ p ∈ survivingParticles β ∧ generation p.2 = k :=
  Iff.rfl

/-- A generation slice consists of surviving particles. -/
theorem mem_survivingParticles_of_mem_survivingParticlesAt
    (β : RootIndexed.BranchingWalk Root α X) {k : ℕ} {p : Root × TreeNode α}
    (hp : p ∈ survivingParticlesAt β k) : p ∈ survivingParticles β :=
  hp.1

/-- On a generation slice, the generation of the address is the one cutting it. -/
theorem generation_of_mem_survivingParticlesAt (β : RootIndexed.BranchingWalk Root α X)
    {k : ℕ} {p : Root × TreeNode α} (hp : p ∈ survivingParticlesAt β k) :
    generation p.2 = k :=
  hp.2

/-- Different generations carry disjoint sets of particles. -/
theorem disjoint_survivingParticlesAt (β : RootIndexed.BranchingWalk Root α X) {k l : ℕ}
    (hkl : k ≠ l) : Disjoint (survivingParticlesAt β k) (survivingParticlesAt β l) := by
  rw [Set.disjoint_left]
  intro p hp hq
  exact hkl (by rw [← hp.2, hq.2])

/-- A surviving particle lies in one of the generation slices, so those slices partition the
surviving particles. -/
theorem mem_survivingParticles_iff_exists_mem_survivingParticlesAt
    (β : RootIndexed.BranchingWalk Root α X) (p : Root × TreeNode α) :
    p ∈ survivingParticles β ↔ ∃ k : ℕ, p ∈ survivingParticlesAt β k :=
  ⟨fun hp => ⟨generation p.2, hp, rfl⟩, fun ⟨_, hp⟩ => hp.1⟩

/-- `q` is an ancestor of `p` when `p` is a descendant of `q`. The relation is the converse of
`IsDescendant`, kept as its own name because the statements about ancestors read the other way. -/
def IsAncestor (β : RootIndexed.BranchingWalk Root α X) (p q : Root × TreeNode α) : Prop :=
  IsDescendant β q p

theorem isAncestor_iff_isDescendant (β : RootIndexed.BranchingWalk Root α X)
    (p q : Root × TreeNode α) : IsAncestor β p q ↔ IsDescendant β q p := Iff.rfl

/-- Every particle is an ancestor of itself. -/
theorem isAncestor_refl (β : RootIndexed.BranchingWalk Root α X) (p : Root × TreeNode α) :
    IsAncestor β p p :=
  isDescendant_refl β p

/-- An ancestor sits at the same root as the particle it is an ancestor of. -/
theorem fst_eq_of_isAncestor (β : RootIndexed.BranchingWalk Root α X)
    {p q : Root × TreeNode α} (h : IsAncestor β p q) : q.1 = p.1 :=
  (fst_eq_of_isDescendant β h).symm

/-- An ancestor's generation is the generation of the descendant minus the generations between them,
read the other way round from `generation_eq_generation_add_of_isDescendant`. -/
theorem generation_eq_generation_add_of_isAncestor (β : RootIndexed.BranchingWalk Root α X)
    {p q : Root × TreeNode α} (h : IsAncestor β p q) :
    generation p.2 = generation q.2 + generationAfter q.2 p.2 :=
  generation_eq_generation_add_of_isDescendant β h

/-- Ancestors compose: an ancestor of an ancestor is an ancestor, which is what makes the ancestors
of a particle a chain. -/
theorem isAncestor_trans (β : RootIndexed.BranchingWalk Root α X)
    {p q r : Root × TreeNode α} (hpq : IsAncestor β p q) (hqr : IsAncestor β q r) :
    IsAncestor β p r :=
  isDescendant_trans β hqr hpq

/-- The ancestors of a particle: the particles of which it is a descendant. -/
def ancestors (β : RootIndexed.BranchingWalk Root α X) (p : Root × TreeNode α) :
    Set (Root × TreeNode α) :=
  {q | IsAncestor β p q}

@[simp] theorem mem_ancestors_iff (β : RootIndexed.BranchingWalk Root α X)
    (p q : Root × TreeNode α) : q ∈ ancestors β p ↔ IsDescendant β q p := Iff.rfl

/-- The ancestors of a particle exactly `k` generations above it. -/
def ancestorsAt (β : RootIndexed.BranchingWalk Root α X) (p : Root × TreeNode α) (k : ℕ) :
    Set (Root × TreeNode α) :=
  {q | IsAncestor β p q ∧ generationAfter q.2 p.2 = k}

@[simp] theorem mem_ancestorsAt_iff (β : RootIndexed.BranchingWalk Root α X)
    (p : Root × TreeNode α) (k : ℕ) (q : Root × TreeNode α) :
    q ∈ ancestorsAt β p k ↔ IsAncestor β p q ∧ generationAfter q.2 p.2 = k :=
  Iff.rfl

/-- A distance slice consists of ancestors. -/
theorem mem_ancestors_of_mem_ancestorsAt (β : RootIndexed.BranchingWalk Root α X)
    {p : Root × TreeNode α} {k : ℕ} {q : Root × TreeNode α} (hq : q ∈ ancestorsAt β p k) :
    q ∈ ancestors β p :=
  hq.1

/-- On a distance slice, the number of generations above the particle is the one cutting it. -/
theorem generationAfter_of_mem_ancestorsAt (β : RootIndexed.BranchingWalk Root α X)
    {p : Root × TreeNode α} {k : ℕ} {q : Root × TreeNode α} (hq : q ∈ ancestorsAt β p k) :
    generationAfter q.2 p.2 = k :=
  hq.2

/-- Different distances above a particle give disjoint sets of ancestors. -/
theorem disjoint_ancestorsAt (β : RootIndexed.BranchingWalk Root α X) (p : Root × TreeNode α)
    {k l : ℕ} (hkl : k ≠ l) : Disjoint (ancestorsAt β p k) (ancestorsAt β p l) := by
  rw [Set.disjoint_left]
  intro q hq hr
  exact hkl (by rw [← hq.2, hr.2])

/-- An ancestor lies in one of the distance slices, so those slices partition the ancestors. -/
theorem mem_ancestors_iff_exists_mem_ancestorsAt (β : RootIndexed.BranchingWalk Root α X)
    (p q : Root × TreeNode α) :
    q ∈ ancestors β p ↔ ∃ k : ℕ, q ∈ ancestorsAt β p k :=
  ⟨fun hq => ⟨generationAfter q.2 p.2, hq, rfl⟩, fun ⟨_, hq⟩ => hq.1⟩

end Combinatorics.Branching

module

public import Combinatorics.BranchingWalk.Basic.Descendant

/-!
# Realized particle sets

The particles realized by present parent-child links in a branching walk and
their generation-indexed slices. Here “surviving” means realized in the
genealogy; it does not mean that a particle has descendants at arbitrarily
large generations.
-/

@[expose] public section

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

variable {Root α Mark Position : Type*}

/-- The surviving particles of the walk: the particles realized at some time, which are the
descendants of the always-realized root particles. This is the time-free carrier of the walk, the
one the cloud's time slices are cut out of. -/
def survivingParticles (β : RootIndexed.BranchingWalk Root α Mark Position) : Set (RootIndexed.TreeNode Root α) :=
  {p | IsDescendant β (p.1, []) p}

@[simp] theorem mem_survivingParticles_iff (β : RootIndexed.BranchingWalk Root α Mark Position)
    (p : RootIndexed.TreeNode Root α) : p ∈ survivingParticles β ↔ IsDescendant β (p.1, []) p := Iff.rfl

/-- An address of a root survives exactly when the particle it forms is a surviving particle. -/
theorem mem_survivingParticles_iff_surviveAlong (β : RootIndexed.BranchingWalk Root α Mark Position)
    (r : Root) (v : TreeNode α) :
    (r, v) ∈ survivingParticles β ↔ surviveAlong (β.step r) [] v := by
  rw [mem_survivingParticles_iff, isDescendant_root_iff]

/-- The surviving particles are the union of the descendants of the root particles. -/
theorem mem_survivingParticles_iff_exists_mem_descendants (β : RootIndexed.BranchingWalk Root α Mark Position)
    (p : RootIndexed.TreeNode Root α) :
    p ∈ survivingParticles β ↔ ∃ r : Root, p ∈ descendants β (r, []) := by
  constructor
  · intro hp
    exact ⟨p.1, by simpa using hp⟩
  · rintro ⟨r, hr⟩
    have hqr : IsDescendant β (r, []) p := (mem_descendants_iff β (r, []) p).mp hr
    have h1 : p.1 = r := fst_eq_of_isDescendant β hqr
    simpa [mem_survivingParticles_iff, h1] using hqr

/-- The particles present in generation `k`: realized particles whose address
has generation `k`. This is the time-free description of the walk's population
at that generation. -/
def survivingParticlesAt (β : RootIndexed.BranchingWalk Root α Mark Position) (k : ℕ) :
    Set (RootIndexed.TreeNode Root α) :=
  {p | p ∈ survivingParticles β ∧ generation p.2 = k}

@[simp] theorem mem_survivingParticlesAt_iff (β : RootIndexed.BranchingWalk Root α Mark Position) (k : ℕ)
    (p : RootIndexed.TreeNode Root α) :
    p ∈ survivingParticlesAt β k ↔ p ∈ survivingParticles β ∧ generation p.2 = k :=
  Iff.rfl

/-- A generation slice consists of surviving particles. -/
theorem mem_survivingParticles_of_mem_survivingParticlesAt
    (β : RootIndexed.BranchingWalk Root α Mark Position) {k : ℕ} {p : RootIndexed.TreeNode Root α}
    (hp : p ∈ survivingParticlesAt β k) : p ∈ survivingParticles β :=
  hp.1

/-- On a generation slice, the generation of the address is the one cutting it. -/
theorem generation_of_mem_survivingParticlesAt (β : RootIndexed.BranchingWalk Root α Mark Position)
    {k : ℕ} {p : RootIndexed.TreeNode Root α} (hp : p ∈ survivingParticlesAt β k) :
    generation p.2 = k :=
  hp.2

/-- Different generations carry disjoint sets of particles. -/
theorem disjoint_survivingParticlesAt (β : RootIndexed.BranchingWalk Root α Mark Position) {k l : ℕ}
    (hkl : k ≠ l) : Disjoint (survivingParticlesAt β k) (survivingParticlesAt β l) := by
  rw [Set.disjoint_left]
  intro p hp hq
  exact hkl (by rw [← hp.2, hq.2])

/-- A surviving particle lies in one of the generation slices, so those slices partition the
surviving particles. -/
theorem mem_survivingParticles_iff_exists_mem_survivingParticlesAt
    (β : RootIndexed.BranchingWalk Root α Mark Position) (p : RootIndexed.TreeNode Root α) :
    p ∈ survivingParticles β ↔ ∃ k : ℕ, p ∈ survivingParticlesAt β k :=
  ⟨fun hp => ⟨generation p.2, hp, rfl⟩, fun ⟨_, hp⟩ => hp.1⟩

end Combinatorics.Branching

end

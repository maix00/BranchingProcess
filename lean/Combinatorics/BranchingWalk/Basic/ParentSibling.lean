module

public import Combinatorics.BranchingWalk.Basic.Survival
public import Combinatorics.BranchingWalk.Basic.Ancestor

/-!
# Parent and sibling relations

Immediate parent and sibling relations for surviving particles.
-/

@[expose] public section

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

variable {Root α Mark Position : Type*}

/-- The parent of a particle: the address without its last label. The function is total, a root being
its own parent, and it is decided by the address alone, not by the walk. -/
def parent (p : RootIndexed.TreeNode Root α) : RootIndexed.TreeNode Root α :=
  (p.1, p.2.dropLast)

@[simp] theorem fst_parent (p : RootIndexed.TreeNode Root α) : (parent p).1 = p.1 := rfl

@[simp] theorem snd_parent (p : RootIndexed.TreeNode Root α) : (parent p).2 = p.2.dropLast := rfl

/-- A root is its own parent. -/
@[simp] theorem parent_root (r : Root) : parent (r, ([] : TreeNode α)) = (r, []) := by
  simp [parent]

/-- The parent of a child is the node it hangs from. -/
@[simp] theorem parent_child (r : Root) (u : TreeNode α) (i : α) :
    parent (r, u ++ [i]) = (r, u) := by
  simp [parent]

/-- `q` is a child of `p` in the walk: the address of `q` is the address of `p` followed by one label
whose slot survives. This is the ancestor at distance one, `generationAfter p q = 1`. -/
def IsParent (β : RootIndexed.BranchingWalk Root α Mark Position) (p q : RootIndexed.TreeNode Root α) : Prop :=
  ∃ i, q = (p.1, p.2 ++ [i]) ∧ survive (β.step p.1 p.2) i

/-- A child is a descendant. -/
theorem isParent_isDescendant (β : RootIndexed.BranchingWalk Root α Mark Position)
    {p q : RootIndexed.TreeNode Root α} (h : IsParent β p q) : IsDescendant β p q := by
  obtain ⟨i, rfl, hi⟩ := h
  exact ⟨[i], rfl, by simpa [surviveAlong] using hi⟩

/-- Read in the ancestor direction: a parent is a direct ancestor of its child. -/
theorem isParent_isAncestor (β : RootIndexed.BranchingWalk Root α Mark Position)
    {p q : RootIndexed.TreeNode Root α} (h : IsParent β p q) : IsAncestor β q p :=
  isParent_isDescendant β h

/-- A child sits one generation below its parent. -/
theorem isParent_generationAfter (β : RootIndexed.BranchingWalk Root α Mark Position)
    {p q : RootIndexed.TreeNode Root α} (h : IsParent β p q) :
    RootIndexed.generationAfter p q = 1 := by
  obtain ⟨i, rfl, -⟩ := h
  exact RootIndexed.generationAfter_append_singleton p i

/-- The parent of a surviving child is a parent in the walk: the label survives in the step at the
parent's address. This is what makes the slots of one step readable as particles. -/
theorem isParent_of_mem_survivingParticles (β : RootIndexed.BranchingWalk Root α Mark Position) {r : Root}
    {u : TreeNode α} {i : α} (h : (r, u ++ [i]) ∈ survivingParticles β) :
    IsParent β (r, u) (r, u ++ [i]) := by
  have hs : surviveAlong (β.step r) [] (u ++ [i]) :=
    (mem_survivingParticles_iff_surviveAlong β r (u ++ [i])).mp h
  rw [surviveAlong_root_append_singleton_iff] at hs
  exact ⟨i, rfl, hs.2⟩

/-- Two particles are siblings when they share a parent. -/
def IsSibling (β : RootIndexed.BranchingWalk Root α Mark Position) (p q : RootIndexed.TreeNode Root α) : Prop :=
  ∃ s, IsParent β s p ∧ IsParent β s q

/-- Siblinghood is symmetric. -/
theorem isSibling_symm (β : RootIndexed.BranchingWalk Root α Mark Position)
    {p q : RootIndexed.TreeNode Root α} (h : IsSibling β p q) : IsSibling β q p := by
  obtain ⟨s, h1, h2⟩ := h
  exact ⟨s, h2, h1⟩

/-- Siblinghood, as a symmetric relation. -/
theorem isSibling_comm (β : RootIndexed.BranchingWalk Root α Mark Position)
    (p q : RootIndexed.TreeNode Root α) : IsSibling β p q ↔ IsSibling β q p :=
  ⟨isSibling_symm β, isSibling_symm β⟩

/-- Particles hanging from a common parent are siblings. -/
theorem isSibling_of_isParent (β : RootIndexed.BranchingWalk Root α Mark Position)
    {s p q : RootIndexed.TreeNode Root α} (hp : IsParent β s p) (hq : IsParent β s q) :
    IsSibling β p q :=
  ⟨s, hp, hq⟩

/-- The surviving siblings of a particle: its siblings that are themselves alive. -/
def survivingSiblings (β : RootIndexed.BranchingWalk Root α Mark Position) (p : RootIndexed.TreeNode Root α) :
    Set (RootIndexed.TreeNode Root α) :=
  {q | IsSibling β p q ∧ q ∈ survivingParticles β}

@[simp] theorem mem_survivingSiblings_iff (β : RootIndexed.BranchingWalk Root α Mark Position)
    (p q : RootIndexed.TreeNode Root α) :
    q ∈ survivingSiblings β p ↔ IsSibling β p q ∧ q ∈ survivingParticles β :=
  Iff.rfl

/-- The surviving children of the parent of a surviving particle belong to its surviving siblings:
with the slots of the step at the parent's address, this is the correspondence between the cloud's
index and the slots of one step. -/
theorem mem_survivingSiblings_of_survives (β : RootIndexed.BranchingWalk Root α Mark Position) {r : Root}
    {u : TreeNode α} {i j : α} (hi : (r, u ++ [i]) ∈ survivingParticles β)
    (hj : survive (β.step r u) j) (hjs : (r, u ++ [j]) ∈ survivingParticles β) :
    (r, u ++ [j]) ∈ survivingSiblings β (r, u ++ [i]) :=
  ⟨isSibling_of_isParent β (isParent_of_mem_survivingParticles β hi) ⟨j, rfl, hj⟩, hjs⟩

end Combinatorics.Branching

end

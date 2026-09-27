import Combinatorics.BranchingWalk.Cloud.Rank.Basic

/-!
# Rank of a particle in one time slice

A particle of the cloud is an initial root together with an address, so a rank
counts particles below a fixed particle of `Root × TreeNode α`. The order on
that type is not yet fixed by the cloud (the walk's selection compares
positions), so it is an explicit hypothesis here. -/

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

variable {Time Root α X : Type*}

/-- Cardinal rank of a particle in a complete time slice: the number of
particles of the slice that lie strictly below it. -/
noncomputable def Cloud.sliceRank [LT (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time) (q : Root × TreeNode α) : ℕ∞ :=
  {p | p ∈ C.particles t ∧ p < q}.encard

@[simp] theorem Cloud.sliceRank_def [LT (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time) (q : Root × TreeNode α) :
    C.sliceRank t q = {p | p ∈ C.particles t ∧ p < q}.encard := rfl

/-- The rank respects the index order: a particle of a slice that lies below another
particle of the same slice has the smaller rank. Particles at the same position are
still separated by their index, hence by their rank. -/
theorem Cloud.sliceRank_mono [Preorder (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time) {p q : Root × TreeNode α} (hpq : p < q) :
    C.sliceRank t p ≤ C.sliceRank t q :=
  Set.encard_le_encard fun _ hr => ⟨hr.1, lt_trans hr.2 hpq⟩


/-- On a finite slice of a linearly ordered cloud the rank separates the particles: two
particles of the slice with the same rank are the same particle, so the ranks enumerate the
slice and several particles at one position stay distinct. -/
theorem Cloud.sliceRank_injOn_of_finite [LinearOrder (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time) [Fintype (C.particles t)] :
    Set.InjOn (C.sliceRank t) (C.particles t) := by
  have hfinC : (C.particles t).Finite := Set.toFinite (C.particles t)
  intro p hp q hq hpq
  by_contra hne
  have hcast : ∀ r : Root × TreeNode α,
      ({s | s ∈ C.particles t ∧ s < r} : Set (Root × TreeNode α)).encard =
        (({s | s ∈ C.particles t ∧ s < r} : Set (Root × TreeNode α)).ncard : ℕ∞) := by
    intro r
    have hf : ({s | s ∈ C.particles t ∧ s < r} : Set (Root × TreeNode α)).Finite :=
      hfinC.subset fun s hs => hs.1
    rw [Set.ncard_eq_toFinset_card _ hf, Set.Finite.encard_eq_coe_toFinset_card hf]
  simp only [Cloud.sliceRank_def] at hpq
  have he : ({s | s ∈ C.particles t ∧ s < p} : Set (Root × TreeNode α)).ncard =
      ({s | s ∈ C.particles t ∧ s < q} : Set (Root × TreeNode α)).ncard := by
    have h := hpq
    rw [hcast p, hcast q] at h
    exact ENat.natCast_inj.mp h
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hss : ({s | s ∈ C.particles t ∧ s < p} : Set (Root × TreeNode α)) ⊂
        {s | s ∈ C.particles t ∧ s < q} := by
      refine ⟨fun s hs => ⟨hs.1, lt_trans hs.2 hlt⟩, fun hsub => ?_⟩
      exact absurd (hsub ⟨hp, hlt⟩).2 (lt_irrefl p)
    have hfq : ({s | s ∈ C.particles t ∧ s < q} : Set (Root × TreeNode α)).Finite :=
      hfinC.subset fun s hs => hs.1
    exact (ne_of_lt (Set.ncard_lt_ncard hss hfq)) he
  · have hss : ({s | s ∈ C.particles t ∧ s < q} : Set (Root × TreeNode α)) ⊂
        {s | s ∈ C.particles t ∧ s < p} := by
      refine ⟨fun s hs => ⟨hs.1, lt_trans hs.2 hgt⟩, fun hsub => ?_⟩
      exact absurd (hsub ⟨hq, hgt⟩).2 (lt_irrefl q)
    have hfp : ({s | s ∈ C.particles t ∧ s < p} : Set (Root × TreeNode α)).Finite :=
      hfinC.subset fun s hs => hs.1
    exact (ne_of_lt (Set.ncard_lt_ncard hss hfp)) he.symm

theorem Cloud.sliceRank_eq_finsetRank [LinearOrder (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time)
    (s : Finset (Root × TreeNode α))
    (hs : C.particles t = (s : Set (Root × TreeNode α)))
    (q : Root × TreeNode α) :
    C.sliceRank t q = (finsetRank s q : ℕ∞) := by
  rw [Cloud.sliceRank, hs]
  rw [Set.encard_eq_coe_toFinset_card]
  simp [finsetRank]

/-- The rank of a particle is at most the number of particles of the slice lying weakly
below it in position. This is the first half of the link between the rankwise order and the
threshold counts: with positions increasing along the index order, everything strictly below
a particle in the index order is below it in position as well. -/
theorem Cloud.sliceRank_le_encard_position_of_mono [Preorder X]
    [Preorder (Root × TreeNode α)] (C : Cloud Time Root α X) (t : Time)
    (hmono : ∀ p, p ∈ C.particles t → ∀ q, q ∈ C.particles t →
      p < q → C.position p.1 p.2 ≤ C.position q.1 q.2)
    {p : Root × TreeNode α} (hp : p ∈ C.particles t) :
    C.sliceRank t p ≤
      {q | q ∈ C.particles t ∧ C.position q.1 q.2 ≤ C.position p.1 p.2}.encard :=
  Set.encard_le_encard fun _ hq => ⟨hq.1, hmono _ hq.1 _ hp hq.2⟩

end Combinatorics.Branching

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
  Set.encard_le_encard fun r hr => ⟨hr.1, lt_trans hr.2 hpq⟩

theorem Cloud.sliceRank_eq_finsetRank [LinearOrder (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time)
    (s : Finset (Root × TreeNode α))
    (hs : C.particles t = (s : Set (Root × TreeNode α)))
    (q : Root × TreeNode α) :
    C.sliceRank t q = (finsetRank s q : ℕ∞) := by
  rw [Cloud.sliceRank, hs]
  rw [Set.encard_eq_coe_toFinset_card]
  simp [finsetRank]

end Combinatorics.Branching

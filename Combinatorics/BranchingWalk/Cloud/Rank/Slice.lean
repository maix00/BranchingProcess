import Combinatorics.BranchingWalk.Cloud.Rank.Basic

namespace Combinatorics.Branching

variable {Time Index X : Type*}

/-- Cardinal rank of an indexed particle in a complete time slice. -/
noncomputable def Cloud.sliceRank [LT Index]
    (C : Cloud Time Index X) (t : Time) (q : Index) : ℕ∞ :=
  {p | p ∈ C.particles t ∧ p < q}.encard

@[simp] theorem Cloud.sliceRank_def [LT Index]
    (C : Cloud Time Index X) (t : Time) (q : Index) :
    C.sliceRank t q = {p | p ∈ C.particles t ∧ p < q}.encard := rfl

theorem Cloud.sliceRank_eq_finsetRank [LinearOrder Index]
    (C : Cloud Time Index X) (t : Time) (s : Finset Index)
    (hs : C.particles t = (s : Set Index)) (q : Index) :
    C.sliceRank t q = (finsetRank s q : ℕ∞) := by
  rw [Cloud.sliceRank, hs]
  rw [Set.encard_eq_coe_toFinset_card]
  simp [finsetRank]

end Combinatorics.Branching

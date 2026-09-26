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

end Combinatorics.Branching

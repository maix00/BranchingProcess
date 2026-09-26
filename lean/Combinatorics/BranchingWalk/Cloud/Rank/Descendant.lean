import Combinatorics.BranchingWalk.Cloud.Rank.Slice

namespace Combinatorics.Branching

variable {Time Index X : Type*}

/-- Cardinal rank restricted to a descendant predicate. -/
noncomputable def Cloud.descendantRank [LT Index]
    (C : Cloud Time Index X) (t : Time)
    (descendant : Index → Prop) [DecidablePred descendant]
    (q : Index) : ℕ∞ :=
  {p | p ∈ C.particles t ∧ descendant p ∧ p < q}.encard

@[simp] theorem Cloud.descendantRank_def [LT Index]
    (C : Cloud Time Index X) (t : Time)
    (descendant : Index → Prop) [DecidablePred descendant]
    (q : Index) :
    C.descendantRank t descendant q =
      {p | p ∈ C.particles t ∧ descendant p ∧ p < q}.encard := rfl

end Combinatorics.Branching

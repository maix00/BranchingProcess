import Combinatorics.BranchingWalk.Cloud.Rank.Slice

namespace Combinatorics.Branching

variable {Time Index X : Type*}

theorem Cloud.descendantRank_eq_siblingRank
    {ι X : Type*} [LT ι] (ξ : Step ι X) (i : ι)
    (C : Cloud Time ι X) (t : Time)
    (h : {p | p ∈ C.particles t ∧ p < i} =
      {p | survive ξ p ∧ p < i}) :
    C.sliceRank t i = ξ.siblingRank i := by
  rw [Cloud.sliceRank, Step.siblingRank, h]

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

import Combinatorics.BranchingWalk.Cloud.Basic

/-!
# Rank restricted to the descendants of a particle

The descendants of a particle are the particles below it in the genealogical
order, so a rank restricted to them counts the particles of a time slice that
are descendants and lie below a fixed particle of `Root × TreeNode α`. As in
`Rank/Slice.lean`, the order on that type is an explicit hypothesis. -/

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

variable {Time Root α X : Type*}

/-- Cardinal rank restricted to a descendant predicate. -/
noncomputable def Cloud.descendantRank [LT (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time)
    (descendant : Root × TreeNode α → Prop) [DecidablePred descendant]
    (q : Root × TreeNode α) : ℕ∞ :=
  {p | p ∈ C.particles t ∧ descendant p ∧ p < q}.encard

@[simp] theorem Cloud.descendantRank_def [LT (Root × TreeNode α)]
    (C : Cloud Time Root α X) (t : Time)
    (descendant : Root × TreeNode α → Prop) [DecidablePred descendant]
    (q : Root × TreeNode α) :
    C.descendantRank t descendant q =
      {p | p ∈ C.particles t ∧ descendant p ∧ p < q}.encard := rfl

end Combinatorics.Branching

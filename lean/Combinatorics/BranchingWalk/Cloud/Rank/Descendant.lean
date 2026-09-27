import Combinatorics.BranchingWalk.Cloud.Basic
import Combinatorics.BranchingWalk.Step.Rank

/-!
# Rank restricted to the descendants of a particle

The descendants of a particle are the particles below it in the genealogical
order, so a rank restricted to them counts the particles of a time slice that
are descendants and lie below a fixed particle of `RootIndexed.TreeNode Root α`. As in
`Rank/Slice.lean`, the order on that type is an explicit hypothesis. -/

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

variable {Time Root α X : Type*}

/-- Cardinal rank restricted to a descendant predicate. -/
noncomputable def Cloud.descendantRank [LT (RootIndexed.TreeNode Root α)]
    (C : Cloud Time Root α X) (t : Time)
    (descendant : RootIndexed.TreeNode Root α → Prop) [DecidablePred descendant]
    (q : RootIndexed.TreeNode Root α) : ℕ∞ :=
  {p | p ∈ C.particles t ∧ descendant p ∧ p < q}.encard

@[simp] theorem Cloud.descendantRank_def [LT (RootIndexed.TreeNode Root α)]
    (C : Cloud Time Root α X) (t : Time)
    (descendant : RootIndexed.TreeNode Root α → Prop) [DecidablePred descendant]
    (q : RootIndexed.TreeNode Root α) :
    C.descendantRank t descendant q =
      {p | p ∈ C.particles t ∧ descendant p ∧ p < q}.encard := rfl

/-- The descendant rank of a cloud is the sibling rank of a step as soon as the particles of the
slice that the descendant predicate selects, below the point, are exactly the step's survive
slots below it. The finiteness hypothesis is the same as in the slice-rank comparison: the
slots are counted below a point, so it is the finiteness of an interval bounded above. -/
theorem Cloud.descendantRank_eq_siblingRank
    [Preorder (RootIndexed.TreeNode Root α)] [LocallyFiniteOrderBot (RootIndexed.TreeNode Root α)]
    (C : Cloud Time Root α X) (t : Time) (ξ : Step (RootIndexed.TreeNode Root α) X)
    (descendant : RootIndexed.TreeNode Root α → Prop) [DecidablePred descendant]
    (i : RootIndexed.TreeNode Root α)
    (h : {p | p ∈ C.particles t ∧ descendant p ∧ p < i} =
      {p | survive ξ p ∧ p < i}) :
    C.descendantRank t descendant i = (ξ.siblingRank i : ℕ∞) := by
  have hIio : (Set.Iio i).Finite := by
    simpa only [Finset.coe_Iio] using (Finset.Iio i).finite_toSet
  have hfin : {p | survive ξ p ∧ p < i}.Finite := hIio.subset fun _ hp => hp.2
  rw [Cloud.descendantRank, Step.siblingRank, h,
    Set.Finite.encard_eq_coe_toFinset_card hfin,
    Set.ncard_eq_toFinset_card (hs := hfin)]

end Combinatorics.Branching

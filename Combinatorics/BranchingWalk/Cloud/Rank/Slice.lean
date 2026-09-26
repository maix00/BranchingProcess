import Combinatorics.BranchingWalk.Cloud.Rank.Basic
import Combinatorics.BranchingWalk.Step.Rank

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

/-- The slice rank of an indexed cloud is the sibling rank of the step as soon
as the cloud's slice has the same membership as the step's survive slots.

The predecessor set has to be finite, and the convention here is mathlib's own
class for that: the slots are counted below a point, so this is the finiteness
of an interval bounded above, which `LocallyFiniteOrderBot` supplies as
`Finset.Iio`. Without it the identity is false, because `siblingRank` is
`ℕ`-valued and is `0` by definition on an infinite predecessor set, whereas
`sliceRank` is the `ℕ∞`-valued cardinal; the finiteness-free statement is the
`Cardinal`-valued `Step.siblingCardinal`. -/
theorem Cloud.sliceRank_eq_siblingRank
    {ι X : Type*} [Preorder ι] [LocallyFiniteOrderBot ι] (ξ : Step ι X) (i : ι)
    (C : Cloud Time ι X) (t : Time)
    (h : {p | p ∈ C.particles t ∧ p < i} =
      {p | survive ξ p ∧ p < i}) :
    C.sliceRank t i = ξ.siblingRank i := by
  have hIio : (Set.Iio i).Finite := by
    simpa only [Finset.coe_Iio] using (Finset.Iio i).finite_toSet
  have hfin : {p | survive ξ p ∧ p < i}.Finite :=
    hIio.subset fun _ hp => hp.2
  rw [Cloud.sliceRank, Step.siblingRank, h,
    hfin.encard_eq_coe_toFinset_card, Set.ncard_eq_toFinset_card _ hfin]

end Combinatorics.Branching

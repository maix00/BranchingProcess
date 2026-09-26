import Combinatorics.BranchingWalk.Step.Relation
import Mathlib.Order.Interval.Set.Nat

/-!
# The ordinal of a sibling in one branching step

`Step.siblingRank ξ i` counts the survive slots strictly before `i`.  It only
uses the slot order and the survive predicate; ordering the child marks is a
separate condition and is deliberately absent from this definition.

The definition is polymorphic in the slot type.  For the canonical
`ℕ`-indexed representation, sibling closure makes the slot number itself the
sibling rank.  A merely countable slot type does not have a canonical rank:
one must additionally choose an order whose predecessor sets are finite.
-/

namespace Combinatorics

namespace Branching

/-- The zero-based ordinal of slot `i` among the survive siblings: the number
of survive slots strictly before it.

If that predecessor set is infinite, `Set.ncard` is zero.  Applications that
use this as an ordinal therefore prove finiteness; this is automatic for a
slot in an `ℕ`-indexed step. -/
noncomputable def Step.siblingRank {ι X : Type*} [LT ι]
    (ξ : Step ι X) (i : ι) : ℕ :=
  {j | survive ξ j ∧ j < i}.ncard

/-- In a sibling-closed `ℕ`-indexed step, every survive slot has rank equal to
its slot number.  No monotonicity assumption on the marks is involved. -/
@[simp] theorem Step.siblingRank_eq_nat_of_isSiblingClosed
    {X : Type*} (ξ : NatStep X) (hclosed : Step.IsSiblingClosed ξ)
    {i : ℕ} (hi : survive ξ i) :
    ξ.siblingRank i = i := by
  rw [Step.siblingRank, show {j : ℕ | survive ξ j ∧ j < i} = Set.Iio i by
    ext j
    constructor
    · exact fun hj => hj.2
    · intro hj
      exact ⟨by
        cases hjvalue : ξ j with
        | none =>
            have hinone := hclosed j i hj hjvalue
            exact ((survive_iff_ne_none ξ i).mp hi hinone).elim
        | some x => exact ⟨x, hjvalue⟩, hj⟩]
  exact Set.ncard_Iio_nat i

end Branching

end Combinatorics

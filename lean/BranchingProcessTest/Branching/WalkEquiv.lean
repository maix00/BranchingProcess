import Combinatorics.BranchingWalk.Walk.Equiv

/-!
# Tests for the singleton-walk encoding

The tests exercise both inverses of the exact representation by an initial
position and optional increments.
-/

example {Mark Position : Type*}
    (walk : Combinatorics.Branching.Walk Mark Position) :
    (Combinatorics.Branching.Walk.equivInitialOptionalIncrements
      (Mark := Mark) (Position := Position)).symm
      (Combinatorics.Branching.Walk.equivInitialOptionalIncrements walk) = walk := by
  exact Combinatorics.Branching.Walk.equivInitialOptionalIncrements.left_inv walk

example {Mark Position : Type*} (data : Position × (ℕ → Option Mark)) :
    Combinatorics.Branching.Walk.equivInitialOptionalIncrements
      (Mark := Mark) (Position := Position)
      ((Combinatorics.Branching.Walk.equivInitialOptionalIncrements).symm data) = data := by
  exact Combinatorics.Branching.Walk.equivInitialOptionalIncrements.right_inv data

#print axioms Combinatorics.Branching.Walk.nodeEquivNat
#print axioms Combinatorics.Branching.Walk.equivInitialOptionalIncrements

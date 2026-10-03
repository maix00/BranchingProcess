module

public import Combinatorics.Branching.Basic
public import Combinatorics.BranchingWalk.Basic.Map

/-!
# Mapping a branching walk to its genealogy

Forgetting spatial marks turns a branching walk into the corresponding
unit-marked branching process. This is a projection from the spatial model to
its genealogy.
-/

@[expose] public section

namespace Combinatorics.Branching

/-- Forget the marks of a root-indexed branching walk. The result retains the
same genealogy and initial roots, represented by unit marks. -/
def RootIndexed.BranchingWalk.toBranching
    {Root α Mark Position : Type*}
    (β : RootIndexed.BranchingWalk Root α Mark Position) :
    RootIndexed.Process Root α where
  step r := (β.step r).forgetMarks
  initial _ := PUnit.unit

@[simp] theorem RootIndexed.BranchingWalk.surviveAlong_toBranching_iff
    {Root α Mark Position : Type*}
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (r : Root) (v p : Combinatorics.UlamHarris.TreeNode α) :
    surviveAlong (β.toBranching.step r) v p ↔
      surviveAlong (β.step r) v p :=
  surviveAlong_map_iff _ _ _ _

end Combinatorics.Branching

end

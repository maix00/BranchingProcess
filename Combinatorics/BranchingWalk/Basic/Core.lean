module

public import Combinatorics.UlamHarris.Basic
public import Combinatorics.BranchingWalk.Step.Basic

public section

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

/-- A field of branching steps, one optional offspring map at every node. -/
abbrev StepField (α X : Type*) := TreeNode α → Step α X

end Combinatorics.Branching

end

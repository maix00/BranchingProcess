import Combinatorics.UlamHarris.Basic
import Combinatorics.BranchingWalk.Step.Basic

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

/-- A field of branching steps, one optional offspring map at every node. -/
abbrev StepField (α X : Type*) := TreeNode α → Step α X

end Combinatorics.Branching

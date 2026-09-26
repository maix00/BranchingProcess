import Combinatorics.BranchingWalk.Basic.Displace

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

namespace RootIndexed

/-- A displacement field indexed by the initial root. -/
abbrev StepField (Root α X : Type*) := Root → Branching.StepField α X

/-- Total displacement along a root-indexed path. Missing slots contribute
zero through `value'`; this definition is independent of the single-root
`displaceRoot` wrapper. -/
def displace {Root α X : Type*} [AddCommMonoid X]
    (step : StepField Root α X) (r : Root) : TreeNode α → X
  | [] => 0
  | i :: p => value' (step r []) i + displace step r p

@[simp] theorem displace_nil {Root α X : Type*} [AddCommMonoid X]
    (step : StepField Root α X) (r : Root) :
    displace step r [] = 0 := rfl

end RootIndexed

end Combinatorics.Branching

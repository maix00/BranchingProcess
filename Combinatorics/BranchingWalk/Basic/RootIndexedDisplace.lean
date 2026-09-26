import Combinatorics.BranchingWalk.Basic.Displace

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

namespace RootIndexed

/-- A displacement field indexed by the initial root. -/
abbrev StepField (Root α X : Type*) := Root → Branching.StepField α X

/-- Total displacement along a root-indexed path. Missing slots contribute
zero through `value'`; this definition is independent of the single-root
`displaceRoot` wrapper. -/
def displaceAt {Root α X : Type*} [AddCommMonoid X]
    (step : StepField Root α X) (r : Root) :
    TreeNode α → TreeNode α → X
  | _, [] => 0
  | v, i :: p => value' (step r v) i +
      displaceAt step r (v ++ [i]) p

def displace {Root α X : Type*} [AddCommMonoid X]
    (step : StepField Root α X) (r : Root) (u : TreeNode α) : X :=
  displaceAt step r [] u

/-- Partial displacement, recording an absent slot by `none`. -/
def displaceAt? {Root α X : Type*} [AddCommMonoid X]
    (step : StepField Root α X) (r : Root) :
    TreeNode α → TreeNode α → Option X
  | _, [] => some 0
  | v, i :: p =>
      match step r v i with
      | none => none
      | some x => (displaceAt? step r (v ++ [i]) p).map (x + ·)

def displace? {Root α X : Type*} [AddCommMonoid X]
    (step : StepField Root α X) (r : Root)
    (u : TreeNode α) : Option X :=
  displaceAt? step r [] u

@[simp] theorem displace_nil {Root α X : Type*} [AddCommMonoid X]
    (step : StepField Root α X) (r : Root) :
    displace step r [] = 0 := rfl

@[simp] theorem displace?_nil {Root α X : Type*} [AddCommMonoid X]
    (step : StepField Root α X) (r : Root) :
    displace? step r [] = some 0 := rfl

end RootIndexed

end Combinatorics.Branching

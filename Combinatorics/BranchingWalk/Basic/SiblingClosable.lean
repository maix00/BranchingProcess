module

public import Combinatorics.BranchingWalk.Basic.Definitions
public import Combinatorics.BranchingWalk.Step.Relation

/-!
# Sibling closability of a step field and of a walk

`Step.IsSiblingClosable` is the step-level notion, and `IsSiblingClosable` on a slot type is what makes
it automatic there. The two classes here lift it: a step field is sibling closable when every one of its
steps is, and a root-indexed walk when all of its step fields are. Both hold by instance search on a
sibling closable slot type, so nothing has to be handed in — and the relabelings that witness the
closability can be taken by choice, which is what a marked tree of the field is read along.
-/

@[expose] public section

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris
/-- The sibling closure of a step field: every step of the field has its surviving slots as an
initial segment. This is what makes the realized addresses form a `Tree`, and it is to
`Step.IsSiblingClosed` what `IsParentClosed` is to prefix closure. -/
abbrev IsSiblingClosed {α X : Type*} [LT α] (β : StepField α X) : Prop :=
  ∀ u, Step.IsSiblingClosed (β u)


variable {Root α Mark Position : Type*} [LT α]

/-- A step field is sibling closable when every one of its steps is. -/
class StepField.IsSiblingClosable (β : StepField α X) : Prop where
  pointwise : ∀ u, Step.IsSiblingClosable (β u)

instance (priority := 100) [hα : IsSiblingClosable α] (β : StepField α X) :
    StepField.IsSiblingClosable β :=
  ⟨fun _ => inferInstance⟩

/-- A root-indexed walk is sibling closable when all of its step fields are. -/
class RootIndexed.BranchingWalk.IsSiblingClosable (β : RootIndexed.BranchingWalk Root α Mark Position) : Prop where
  pointwise : ∀ r, StepField.IsSiblingClosable (β.step r)

instance (priority := 100) [hα : IsSiblingClosable α] (β : RootIndexed.BranchingWalk Root α Mark Position) :
    RootIndexed.BranchingWalk.IsSiblingClosable β :=
  ⟨fun _ => inferInstance⟩

/-- A sibling closable step field can be relabeled, step by step, into a sibling closed one: the
relabelings are the witnesses of the closability, taken by choice. Reading the relabeled field with
`markedTreeOfStep` is then the marked tree of the field. -/
theorem StepField.exists_relabeling_isSiblingClosed (β : StepField α X)
    (h : StepField.IsSiblingClosable β) :
    ∃ φ : (u : TreeNode α) → α → α, (∀ u, Function.Injective (φ u)) ∧
      ∀ u, Step.IsSiblingClosed fun i => β u (φ u i) := by
  choose φ hinj hclosed using fun u => (h.pointwise u).exists_relabel
  exact ⟨φ, hinj, hclosed⟩

end Branching

end Combinatorics

end

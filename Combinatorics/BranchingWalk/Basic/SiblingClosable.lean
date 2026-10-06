/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.SiblingClosed
public import Combinatorics.BranchingWalk.Step.SiblingClosable

/-!
# Relabelable sibling steps

The field and walk predicates lift the step-level support-preserving
relabeling property pointwise. No slot-type-wide instance is provided: a
relabeling must cover the actual child support of each step.
-/

@[expose] public section

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris

variable {Root α Mark Position : Type*} [LT α]

/-- A step field is sibling closable when every one of its steps is. -/
def StepField.IsSiblingClosable (β : StepField α X) : Prop :=
  ∀ u, Step.IsSiblingClosable (β u)

/-- A root-indexed walk is sibling closable when all of its step fields are. -/
def RootIndexed.BranchingWalk.IsSiblingClosable
    (β : RootIndexed.BranchingWalk Root α Mark Position) : Prop :=
  ∀ r, StepField.IsSiblingClosable (β.step r)

/-- A sibling closable step field can be relabeled, step by step, into a sibling closed one: the
relabelings cover every original child and are the witnesses of the closability, taken by choice. -/
theorem StepField.exists_relabeling_isSiblingClosed (β : StepField α X)
    (h : StepField.IsSiblingClosable β) :
    ∃ φ : (u : TreeNode α) → α → α, (∀ u, Function.Injective (φ u)) ∧
      (∀ u, Step.IsSiblingClosed fun i => β u (φ u i)) ∧
      (∀ u j, survive (β u) j → ∃ i, φ u i = j) := by
  choose φ hinj hclosed hcover using fun u => h u
  exact ⟨φ, hinj, hclosed, hcover⟩

end Branching

end Combinatorics

end

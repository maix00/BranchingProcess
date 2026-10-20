/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.BranchingWalk
public import Combinatorics.BranchingWalk.Step.Selection.SiblingClosed

/-!
# Sibling-closed step fields

`IsSiblingClosed β` means that every local step is sibling-closed in its
existing slot order:
`∀ u, Step.IsSiblingClosed (β u)`. This is the direct property, distinct from
`StepField.IsSiblingClosable`, which says that an injective relabeling can
make each local step sibling-closed.
-/

@[expose] public section

namespace Combinatorics

namespace Branching

/-- Every local step of a field has an initial segment of surviving slots. -/
abbrev IsSiblingClosed {α X : Type*} [LT α] (β : StepField α X) : Prop :=
  ∀ u, Step.IsSiblingClosed (β u)

end Branching

end Combinatorics

end

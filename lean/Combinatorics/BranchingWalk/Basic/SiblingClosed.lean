/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.Definitions
public import Combinatorics.BranchingWalk.Step.SiblingClosed

/-!
# Sibling-closed step fields

The direct sibling-closure predicate for a step field says that every local
step has its surviving slots in an initial segment. It is kept separate from
the optional relabeling interface in SiblingClosable.lean: a field may be
relabelable without being sibling-closed in its original slot order.
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

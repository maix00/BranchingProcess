/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.SiblingClosed

/-!
# Sibling-preserving relabelings

`Step.IsSiblingClosable` records that an injective relabeling can make the
present slots an initial segment while still covering every original child.
This support-coverage clause is needed when the relabeled step is used to
represent the original branching configuration.
-/

@[expose] public section

namespace Combinatorics

namespace Branching

section IsSiblingClosable

variable {ι X : Type*} [LT ι]

/-- A step can be relabeled into sibling-closed form without losing any of its
present slots. -/
def Step.IsSiblingClosable (ξ : Step ι X) : Prop :=
  ∃ f : ι → ι, Function.Injective f ∧
    Step.IsSiblingClosed (fun i => ξ (f i)) ∧
    ∀ j, survive ξ j → ∃ i, f i = j

end IsSiblingClosable

end Branching

end Combinatorics

end

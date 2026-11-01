/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Ordering.Sibling.Closed

/-!
# Sibling-preserving relabelings

`Step.IsSiblingClosable` records that an injective relabeling can make the
present slots an initial segment while still covering every original child.
This support-coverage clause is needed when the relabeled step is used to
represent the original branching configuration.

## Public declarations

A step is sibling-closable when an injective reindexing makes it
sibling-closed and still covers every originally present slot:

\[
\exists f:I\hookrightarrow I,\quad
\operatorname{IsSiblingClosed}(i\mapsto\xi(f(i)))
\quad\land\quad
\forall j,\ \xi(j)\ne\mathrm{none}
\Longrightarrow\exists i,\ f(i)=j.
\]

- `Combinatorics.Branching.Step.IsSiblingClosable ξ` means there is an
  injective `f : ι → ι` such that
  `Combinatorics.Branching.Step.IsSiblingClosed (fun i => ξ (f i))` and
  `∀ j, survive ξ j → ∃ i, f i = j`.
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
